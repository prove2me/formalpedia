-- Prove2me | Theorems.Thm_FeedbackSwitching_theorem_4
-- name    : FeedbackSwitching.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:19.437285+00:00
-- url     : https://prove2.me/theorems/e3989fc7-d3be-4806-baaf-55bf68cb7e83
-- title:
--   Theorem 4 — domination lower bound $\mathrm{Reg}^\star_T(G)\ge\frac{T^{2/3}}{1024\log_2(2T)}\max\{1,\frac{\min\{\gamma,T\}}{\log^2(eK)}\}^{1/3}$
-- statement:
--   Let $G$ be an observable graph on $K\ge2$ actions that is not strongly revealing, let $\gamma=\gamma(G)$, and let $T\ge2$. Then
--   $$
--   \mathrm{Reg}^\star_T(G)\ge\frac{T^{2/3}}{1024\log_2(2T)}\max\Big\{1,\ \frac{\min\{\gamma,T\}}{\log^2(eK)}\Big\}^{1/3}.
--   $$
--   This is the lower bound of the $T^{2/3}$ regime; it matches the upper bound of Theorem 3 up to logarithmic factors.
--
--   **Formalization Note** $\log_2$ is base 2, $\log^2(eK)=(\log(eK))^2$ with the natural logarithm; powers are real powers.
--
--   Differences from the source:
--   - reading: the infimum over learners ("the learner selects I_t based on its past observations and randomization"; no measurability stated) → the infimum over Learner K: randomized policies on a probability space of coins that see only the revealed losses and are jointly measurable in (history, coins); reason: the lower-bound proofs (Proposition 4, Appendix G) average over random loss sequences and take the law of the transcript, which needs joint measurability; the algorithms giving the upper bounds are measurable
--   - encoding: actions [K], rounds 1..T, the learner observes ℓ_t(j) for every (I_t, j) ∈ E → actions Fin K, rounds 0..T−1, the learner receives the vector reveal G ℓ_t I_t (observed coordinates, others masked to 0); reason: the mask is determined by I_t and G, both known to the learner, so the vector carries exactly the observed losses; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Theorem 4, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_FeedbackSwitching_StronglyRevealing
import Definitions.Def_FeedbackSwitching_minimaxRegret

namespace FeedbackSwitching

/-- **Theorem 4 (Domination lower bound)**, p.37 (PDF p.39). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Let `G` be an observable graph on `K ≥ 2` actions that is not strongly revealing, let `γ = γ(G)`,
and let `T ≥ 2`. Then `Reg⋆_T(G) ≥ T^{2/3}/(1024 log₂(2T)) · max{1, min{γ, T}/log²(eK)}^{1/3}`."

**Formalization Note.** `Reg⋆_T(G) = minimaxRegret G T` (infimum over jointly measurable randomized
learners). `log₂` is `Real.logb 2`; `log²(eK)` is `(Real.log (e K))²`; powers are `Real.rpow`. -/
theorem theorem_4 {K T : ℕ} (hK : 2 ≤ K) (G : FeedbackGraph K) (hG : Observable G)
    (hSR : ¬ StronglyRevealing G) (hT : 2 ≤ T) :
    (T : ℝ) ^ ((2 : ℝ) / 3) / (1024 * Real.logb 2 (2 * T)) *
        (max 1 (min (dominationNumber G : ℝ) T / Real.log (Real.exp 1 * K) ^ 2)) ^ ((1 : ℝ) / 3)
      ≤ minimaxRegret G T := by sorry

end FeedbackSwitching
