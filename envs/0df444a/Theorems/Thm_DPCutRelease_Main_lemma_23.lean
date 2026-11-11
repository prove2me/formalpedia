-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_23
-- name    : DPCutRelease.Main.lemma_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:14:26.82031+00:00
-- url     : https://prove2.me/theorems/1982da84-03b6-4564-ab55-f5b5388fb0aa
-- title:
--   Lemma 23 — utility of Algorithm 1 on U-bounded weights: γ·w(S) + O(nU log(nU/δβγε) + (n/γε) log⁷(nU/δβγε))
-- statement:
--   Let $n\ge2$, $U\ge1$, $0<\gamma\le1/4$, $0<\varepsilon\le1$, $0<\delta,\beta<1/10$, with all parameters as in Algorithm 1 (in particular $\varepsilon_{GE}=\varepsilon/(4T_1\sqrt{2T_2\log(2T_1/\delta)})$, $\delta_{GE}=\delta/(2T_1T_2)$, and $M_{stop}$ with a sufficiently large universal constant). Given nonnegative weights $w$ bounded by $U$, Algorithm 1 outputs a nonnegative $\tilde w$ satisfying, with probability at least $1-\beta$, simultaneously for every $S\subseteq[n]$,
--   $$\big|w(S,V\setminus S)-\tilde w(S,V\setminus S)\big|\le\gamma\,w(S,V\setminus S)+C\Big(nU\log\frac{nU}{\delta\beta\gamma\varepsilon}+\frac n{\gamma\varepsilon}\Big(\log\frac{nU}{\delta\beta\gamma\varepsilon}\Big)^7\Big),$$
--   for a constant $C$ depending only on the $\Theta$-constants (region form as in Lemma 17).
--
--   **Formalization Note.** `cutRelease (a1Params θ n U γ ε δ β) w ω`; nonnegativity is stated on every run.
--
--   Differences from the source:
--   - reading: Θ(·) parameters k, K, λ, T₁ of Algorithms 1–2 and "a sufficiently large universal constant C" in M_stop, with universal constants → for every constant structure θ in a region Consts.LargeEnough c₀ f g (c_k, c_K, c_{T₁} ≥ c₀; c_λ ≥ f(c_k, c_K, c_{T₁}); c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)), with c₀, f, g existential and chosen first; reason: Θ(·) fixes constants once for the algorithm; the region form says the lemma holds once the constants are large enough in the order the analysis needs, and finitely many such regions intersect, so Lemmas 17–23 hold for one common choice
--   - reading: "O(nU log(nU/(δβγε)) + (n/(γε))(log(nU/(δβγε)))⁷)" → C·(…) with ∃ C > 0 chosen after the constants θ and before n, U, γ, ε, δ, β, w; reason: O(·) is uniform over the parameter range (p. 34: "uniformly over the stated parameter range")
--   - encoding: "outputs a nonnegative weighted graph" → ∀ ω e, 0 ≤ cutRelease … w ω e (every run); reason: the output is nonnegative on every run, not only on the good event
--   - encoding: random draws of the pseudocode (Lap(b), N(0, X_D), fresh in every call) → deterministic function of a noise source ω ∼ noiseLaw (i.i.d. N(0,1) and Lap(1) entries indexed by List ℕ keys, a distinct key per draw); Lap(b) = b·Lap(1), N(0, X) = X^{1/2}·N(0, I); reason: same joint law of all draws; makes the algorithm a function of its randomness
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 32, Lemma 23

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP
import Definitions.Def_DPCutRelease_Main_Algorithms

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 23 (p. 32): for all sufficiently large Θ-constants there is `C > 0` such that for
`n ≥ 2`, `U ≥ 1`, `0 < γ ≤ 1/4`, `0 < ε ≤ 1`, `0 < δ, β < 1/10` and nonnegative `w ≤ U`, Algorithm 1
outputs a nonnegative vector on every run, and with probability at least `1 − β` every cut has
`|w(S) − w̃(S)| ≤ γ w(S) + C(nU L + (n/(γε)) L⁷)`, `L = log(nU/(δβγε))`. -/
theorem lemma_23 :
    ∃ (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ → ℝ), ∀ θ : Consts, θ.LargeEnough c0 f g →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (U γ ε δ β : ℝ) (w : EdgeVec n), 2 ≤ n → 1 ≤ U → 0 < γ →
        γ ≤ 1 / 4 → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 10 → 0 < β → β < 1 / 10 →
        Nonneg w → (∀ e, w e ≤ U) →
        (∀ ω e, 0 ≤ cutRelease (a1Params θ n U γ ε δ β) w ω e) ∧
        noiseLaw {ω | ∃ S : Finset (Fin n),
            γ * cutValue w S + C * (n * U * Real.log (n * U / (δ * β * γ * ε)) +
              n / (γ * ε) * Real.log (n * U / (δ * β * γ * ε)) ^ 7) <
            |cutValue w S - cutValue (cutRelease (a1Params θ n U γ ε δ β) w ω) S|}
          ≤ ENNReal.ofReal β := by sorry

end DPCutRelease.Main
