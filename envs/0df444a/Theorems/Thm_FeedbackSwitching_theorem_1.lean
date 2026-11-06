-- Prove2me | Theorems.Thm_FeedbackSwitching_theorem_1
-- name    : FeedbackSwitching.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:07.235357+00:00
-- url     : https://prove2.me/theorems/20a03a99-321c-42e9-a0c5-bb433a7dcb14
-- title:
--   Theorem 1 — minimax regret with switching costs: $\sqrt T$, $(\gamma\log K)^{1/3}T^{2/3}$ or $T$
-- statement:
--   Let $G$ be a directed graph on $K\ge2$ actions and let $T\ge2$. Write $\mathrm{Reg}^\star_T(G)$ for the minimax regret with switching costs.
--
--   1. If $G$ is strongly revealing, then
--   $$
--   \tfrac14\sqrt T\le\mathrm{Reg}^\star_T(G)\le2^{40}\sqrt{T\log K}\,\log^2(eKT).
--   $$
--   2. If $G$ is observable but not strongly revealing, and $\gamma=\gamma(G)$, then
--   $$
--   \frac{T^{2/3}}{1024\log_2(2T)}\max\Big\{1,\frac{\min\{\gamma,T\}}{\log^2(eK)}\Big\}^{1/3}\le\mathrm{Reg}^\star_T(G)\le\min\big\{5(\gamma\log K)^{1/3}T^{2/3},\ T\big\}.
--   $$
--   3. If $G$ is not observable, then $T/4\le\mathrm{Reg}^\star_T(G)\le T$.
--
--   The characterization is complete: the rate is $\sqrt T$, $T^{2/3}$ or $T$ according as the graph is strongly revealing, observable but not strongly revealing, or not observable, with the domination number governing the middle regime.
--
--   **Formalization Note** $\log$ is natural, $\log_2$ base 2, $\log^2(x)=(\log x)^2$; powers are real powers.
--
--   Differences from the source:
--   - reading: the infimum over learners ("the learner selects I_t based on its past observations and randomization"; no measurability stated) → the infimum over Learner K: randomized policies on a probability space of coins that see only the revealed losses and are jointly measurable in (history, coins); reason: the lower-bound proofs (Proposition 4, Appendix G) average over random loss sequences and take the law of the transcript, which needs joint measurability; the algorithms giving the upper bounds are measurable
--   - generalization: (iii) Reg⋆_T(G) ≥ T/4 → T/4 ≤ Reg⋆_T(G) ≤ T; reason: the upper half of "(iii) Θ(T)" in Theorem 1 on p.2, which the restatement omits; a learner that never switches has regret at most T; dropping the added conjunct gives the restated clause
--   - encoding: actions [K], rounds 1..T, the learner observes ℓ_t(j) for every (I_t, j) ∈ E → actions Fin K, rounds 0..T−1, the learner receives the vector reveal G ℓ_t I_t (observed coordinates, others masked to 0); reason: the mask is determined by I_t and G, both known to the learner, so the vector carries exactly the observed losses; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Theorem 1 (Characterization, restated), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_FeedbackSwitching_StronglyRevealing
import Definitions.Def_FeedbackSwitching_minimaxRegret

namespace FeedbackSwitching

/-- **Theorem 1 (Characterization, restated)**, p.15 (PDF p.17). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Let `G` be a directed graph on `K ≥ 2` actions, and let `T ≥ 2`.
(i) If `G` is strongly revealing, then `(1/4)√T ≤ Reg⋆_T(G) ≤ 2^{40} √(T log K) log²(eKT)`.
(ii) If `G` is observable but not strongly revealing, and `γ = γ(G)`, then
`T^{2/3}/(1024 log₂(2T)) · max{1, min{γ, T}/log²(eK)}^{1/3} ≤ Reg⋆_T(G) ≤ min{5(γ log K)^{1/3}T^{2/3}, T}`.
(iii) If `G` is not observable, then `Reg⋆_T(G) ≥ T/4`."

**Formalization Note.** `Reg⋆_T(G) = minimaxRegret G T`: the infimum over randomized learners
(seeing only the revealed losses, jointly measurable in history and coins) of the supremum over
loss sequences in `[0,1]^{T×K}` of the regret with switching costs of Eq. (12). Clause (iii) also
states `Reg⋆_T(G) ≤ T` (the upper half of "Θ(T)" in Theorem 1 on p.2; a learner that never
switches). `log` is natural, `log₂` is `Real.logb 2`, powers are `Real.rpow`. -/
theorem theorem_1 {K T : ℕ} (hK : 2 ≤ K) (hT : 2 ≤ T) (G : FeedbackGraph K) :
    (StronglyRevealing G →
      1 / 4 * Real.sqrt T ≤ minimaxRegret G T ∧
      minimaxRegret G T ≤
        2 ^ 40 * Real.sqrt (T * Real.log K) * Real.log (Real.exp 1 * K * T) ^ 2) ∧
    (Observable G → ¬ StronglyRevealing G →
      (T : ℝ) ^ ((2 : ℝ) / 3) / (1024 * Real.logb 2 (2 * T)) *
          (max 1 (min (dominationNumber G : ℝ) T / Real.log (Real.exp 1 * K) ^ 2)) ^ ((1 : ℝ) / 3)
        ≤ minimaxRegret G T ∧
      minimaxRegret G T ≤
        min (5 * ((dominationNumber G : ℝ) * Real.log K) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3))
          T) ∧
    (¬ Observable G → (T : ℝ) / 4 ≤ minimaxRegret G T ∧ minimaxRegret G T ≤ T) := by sorry

end FeedbackSwitching
