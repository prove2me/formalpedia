-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_22
-- name    : DPCutRelease.Main.lemma_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:13:42.823354+00:00
-- url     : https://prove2.me/theorems/ad2e371a-caf2-4d82-adb9-0e4177d84890
-- title:
--   Lemma 22 — Algorithm 1 stops (a_i = 0 or M̃_i ≤ M_stop) within T₁ outer rounds w.p. 1 − T₁T₂β_GE − T₁β₂
-- statement:
--   With probability at least $1-T_1T_2\beta_{GE}-T_1\beta_2$, Algorithm 1 terminates with $a_i=0$ or $\tilde M_i\le M_{stop}$ in at most $T_1=O(\log(nU))$ outer rounds (i.e. it returns at line 7 rather than by exhausting the outer loop). Stated in the parameter range of Lemma 23 ($n\ge2$, $U\ge1$, $0<\gamma\le1/4$, $0<\varepsilon\le1$, $0<\delta,\beta<1/10$, $0\le w\le U$), with constants in region form (Lemma 17).
--
--   **Formalization Note.** `cutReleaseStopped` is `true` exactly when the run returned at line 7.
--
--   Differences from the source:
--   - reading: Θ(·) parameters k, K, λ, T₁ of Algorithms 1–2 and "a sufficiently large universal constant C" in M_stop, with universal constants → for every constant structure θ in a region Consts.LargeEnough c₀ f g (c_k, c_K, c_{T₁} ≥ c₀; c_λ ≥ f(c_k, c_K, c_{T₁}); c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)), with c₀, f, g existential and chosen first; reason: Θ(·) fixes constants once for the algorithm; the region form says the lemma holds once the constants are large enough in the order the analysis needs, and finitely many such regions intersect, so Lemmas 17–23 hold for one common choice
--   - reading: Lemma 22 states no parameter range → 2 ≤ n, 1 ≤ U, 0 < γ ≤ 1/4, 0 < ε ≤ 1, 0 < δ, β < 1/10, 0 ≤ w ≤ U; reason: §5.2 analyses Algorithm 1 in Lemma 23’s range, and the proof uses Lemma 21 (γ ≤ 1/4) and wₑ ≤ U
--   - reading: "terminates with aᵢ = 0 or M̃ᵢ ≤ M_stop in at most T₁ = O(log(nU)) outer rounds" → cutReleaseStopped = true (the run returned at line 7 within its T₁ rounds); reason: T₁ is the algorithm’s own round bound Θ(log(nU))
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 31, Lemma 22

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 22 (p. 31): for all sufficiently large Θ-constants, for the parameters of Algorithm 1 in
the range of Lemma 23 and nonnegative `w ≤ U`, with probability at least
`1 − T₁T₂β_GE − T₁β₂` Algorithm 1 terminates with `a_i = 0` or `M̃_i ≤ M_stop` within its `T₁` outer
rounds. -/
theorem lemma_22 :
    ∃ (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ → ℝ), ∀ θ : Consts, θ.LargeEnough c0 f g →
      ∀ (n : ℕ) (U γ ε δ β : ℝ) (w : EdgeVec n), 2 ≤ n → 1 ≤ U → 0 < γ → γ ≤ 1 / 4 →
        0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 10 → 0 < β → β < 1 / 10 →
        Nonneg w → (∀ e, w e ≤ U) →
        noiseLaw {ω | cutReleaseStopped (a1Params θ n U γ ε δ β) w ω = false}
          ≤ ENNReal.ofReal ((a1Params θ n U γ ε δ β).T1 * (a1Params θ n U γ ε δ β).T2 *
              (a1Params θ n U γ ε δ β).betaGE +
              (a1Params θ n U γ ε δ β).T1 * (a1Params θ n U γ ε δ β).beta2) := by sorry

end DPCutRelease.Main
