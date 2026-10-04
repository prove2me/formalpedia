-- Prove2me | Theorems.Thm_DelayedSWPT_Extended_reduction
-- name    : DelayedSWPT.Extended.reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:09:21.580465+00:00
-- url     : https://prove2.me/theorems/b6d043dc-a4a4-4764-8d6f-0ef2c64fde99
-- title:
--   Lemma 3 — a schedule of (E) satisfying inequality (1) gives the factor 2
-- statement:
--   Let (P) be an instance, (2P) its doubled problem, (E) its extended problem with gap jobs $G$, and $\pi_E$ the schedule of (E) induced by Delayed SWPT. Let $\mu^*$ be an optimal schedule for (2P), and suppose $\sigma_E$ is a feasible schedule for (E) such that
--
--   $$\sum_{j\in J} w_j C_j(\sigma_E) + \sum_{g\in G} w_g C_g(\sigma_E) \le \sum_{j\in J} w_j C_j(\mu^*) + \sum_{g\in G} w_g C_g(\pi_E). \tag{1}$$
--
--   Then the Delayed SWPT schedule $\pi$ of (P) satisfies
--
--   $$\sum_{j\in J} w_j C_j(\pi) \le 2 \sum_{j\in J} w_j C_j(S)$$
--
--   for every feasible schedule $S$ of (P).
--
--   This is the reduction on which the whole proof rests: it remains to construct, from $\mu^*$, a schedule $\sigma_E$ satisfying (1).
--
--   **Formalization Note** The paper's conclusion "Delayed SWPT has a competitive ratio of 2" is stated here for the one instance on which the hypothesis is made; quantifying over all instances gives the upper half of Theorem 8. In (2P), $C_j(\mu^*) = \mu^*_j + 2p_j$; for a gap job, $C_g(\pi_E) = t + 1$.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 690, Lemma 3 and inequality (1)

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Lemma 3 of Anderson and Potts (2004), p. 690, for one instance: given an optimal schedule
`μ*` of (2P) and a feasible schedule `σ_E` of (E) satisfying inequality (1)
`∑_{j∈J} wⱼ Cⱼ(σ_E) + ∑_{g∈G} w_g C_g(σ_E) ≤ ∑_{j∈J} wⱼ Cⱼ(μ*) + ∑_{g∈G} w_g C_g(π_E)`,
the Delayed SWPT schedule costs at most twice any feasible schedule of (P). -/
theorem reduction {n : ℕ} (I : Instance n) (μstar : Fin n → ℕ)
    (hμ : IsOptimal (double I).r (double I).p (double I).w μstar)
    (σE : EJob I → ℕ) (hσ : IsFeasible (rE I) (pE I) σE)
    (h1 : ∑ j : Fin n, I.w j * ((σE (Sum.inl j) + I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((σE (Sum.inr g) + 1 : ℕ) : ℝ) ≤
        ∑ j : Fin n, I.w j * ((μstar j + 2 * I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((g.1 + 1 : ℕ) : ℝ))
    (S : Fin n → ℕ) (hS : IsFeasible I.r I.p S) :
    cost I.w I.p (dswpt I) ≤ 2 * cost I.w I.p S := by sorry

end DelayedSWPT.Extended
