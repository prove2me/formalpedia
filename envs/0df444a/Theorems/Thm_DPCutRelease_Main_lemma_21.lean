-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_21
-- name    : DPCutRelease.Main.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:13:52.279703+00:00
-- url     : https://prove2.me/theorems/bbe60bdc-6e3f-4325-ab0f-e6450c2139b9
-- title:
--   Lemma 21 — the MWU of one outer round breaks within T₂ inner iterations w.p. 1 − T₂β_GE − β₂
-- statement:
--   Let $0<\gamma\le1/4$, $\eta=\gamma/[8(1+\gamma)]$, $\tau_2=\log(1/\beta_2)/\varepsilon_2$, $B=O(\tau_1+\lambda n\log n+nU)$, and $M_{stop}=C\big(nU\log\frac{nU}{\delta\beta\gamma\varepsilon}+\frac n{\gamma\varepsilon}(\log\frac{nU}{\delta\beta\gamma\varepsilon})^6\big)\ge10(B+\tau_2/\gamma)$ for a sufficiently large universal constant $C$. For any fixed outer iteration $i$ of Algorithm 1, with probability at least $1-T_2\beta_{GE}-\beta_2$: if $\tilde M_i>M_{stop}$, then within at most $T_2=1+\lceil64(1+\gamma)^2\log n/\gamma^2\rceil$ inner iterations, AggregateWitnesses$(w_i,h_i,\gamma)$ returns $(g^+_i,g^-_i,r_i)$ with
--   $$\langle h_i,r_i\rangle\ge\max\{\langle h_i,g^+_i\rangle,\langle h_i,g^-_i\rangle\}.$$
--   Stated for $n\ge2$, $U\ge1$, $0<\varepsilon\le1$, $0<\delta,\beta<1/10$, nonnegative $w\le U$, and every mask $a_i\in[0,1]^{\binom n2}$ with which round $i$ can start; constants in region form (Lemma 17), which includes $M_{stop}\ge10(B+\tau_2/\gamma)$.
--
--   **Formalization Note.** `massEstimate` is $\tilde M_i$ and `roundBreak` is the inner loop of the round (`none` = no break within $T_2$ steps), both on the round's own noise.
--
--   Differences from the source:
--   - reading: Θ(·) parameters k, K, λ, T₁ of Algorithms 1–2 and "a sufficiently large universal constant C" in M_stop, with universal constants → for every constant structure θ in a region Consts.LargeEnough c₀ f g (c_k, c_K, c_{T₁} ≥ c₀; c_λ ≥ f(c_k, c_K, c_{T₁}); c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)), with c₀, f, g existential and chosen first; reason: Θ(·) fixes constants once for the algorithm; the region form says the lemma holds once the constants are large enough in the order the analysis needs, and finitely many such regions intersect, so Lemmas 17–23 hold for one common choice
--   - reading: "for any fixed outer iteration i" → for every mask a ∈ [0,1]^E, the round run from a with fresh noise; reason: conditional on the history, round i is determined by its mask aᵢ ∈ [0,1] and its own randomness
--   - reading: the parameter range of Algorithm 1 (stated in Lemma 23) → 2 ≤ n, 1 ≤ U, 0 < ε ≤ 1, 0 < δ, β < 1/10, 0 ≤ w ≤ U; reason: Lemma 21 states only γ ≤ 1/4; §5.2 analyses Algorithm 1 in Lemma 23’s range
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 29, Lemma 21

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 21 (p. 29): for all sufficiently large Θ-constants (in particular `M_stop ≥ 10(B + τ₂/γ)`),
for the parameters of Algorithm 1 in the range of Lemma 23, nonnegative `w ≤ U` and every mask
`a ∈ [0,1]^{(n choose 2)}` of a fixed outer round, with probability at least `1 − T₂β_GE − β₂`: if
`M̃_i > M_stop` then within `T₂` inner iterations AggregateWitnesses returns `(g⁺, g⁻, r)` with
`⟨h, r⟩ ≥ max{⟨h, g⁺⟩, ⟨h, g⁻⟩}` (the round breaks). -/
theorem lemma_21 :
    ∃ (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ → ℝ), ∀ θ : Consts, θ.LargeEnough c0 f g →
      ∀ (n : ℕ) (U γ ε δ β : ℝ) (w a : EdgeVec n), 2 ≤ n → 1 ≤ U → 0 < γ → γ ≤ 1 / 4 →
        0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 10 → 0 < β → β < 1 / 10 →
        Nonneg w → (∀ e, w e ≤ U) → (∀ e, 0 ≤ a e ∧ a e ≤ 1) →
        noiseLaw {ω | (a1Params θ n U γ ε δ β).Mstop < massEstimate (a1Params θ n U γ ε δ β) w a ω ∧
            roundBreak (a1Params θ n U γ ε δ β) w a ω = none}
          ≤ ENNReal.ofReal ((a1Params θ n U γ ε δ β).T2 * (a1Params θ n U γ ε δ β).betaGE +
              (a1Params θ n U γ ε δ β).beta2) := by sorry

end DPCutRelease.Main
