-- Prove2me | Theorems.Thm_BanditAlgorithm_pmStoch_expected_actionSetCount_eq_selection_mass
-- name    : BanditAlgorithm.pmStoch_expected_actionSetCount_eq_selection_mass
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T19:21:06.400393+00:00
-- url     : https://prove2.me/theorems/c1f65606-f2de-4875-b629-c37bf18f7849
-- title:
--   Expected action-set count equals cumulative selection mass
-- statement:
--   Let a policy $\pi$ interact for $n$ rounds with a stochastic partial-monitoring environment whose outcomes are independently distributed according to $u$. For any finite set of actions $S$, let $T_S(n)$ count the rounds on which the selected action belongs to $S$. Then
--
--   $$
--   \mathbb E_u[T_S(n)]
--   =
--   \sum_{t=0}^{n-1}\mathbb E_u\!\left[\pi_t(S\mid H_t)\right]
--   =
--   \sum_{t=0}^{n-1}\mathbb E_u\!\left[\sum_{c\in S}\pi_t(c\mid H_t)\right].
--   $$
--
--   This finite-horizon tower-property identity connects action counts on complete histories with the predictable selection masses that occur in adaptive KL chain rules. In particular, choosing $S=[k]\setminus N_{ab}$ gives the expected informative-action count $\mathbb E_{u_a}[\widetilde T(n)]$ used in the hard partial-monitoring lower bound.
--
--   **Formalization Note** The left-hand side writes $T_S(n)$ explicitly as a sum of indicators, while the right-hand side uses the real-valued masses of singleton action events under the policy kernel.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 37.12 proof, printed pp. 490–491: Eq. (37.8) and the definition of T̃(n) in Step 3.

import Definitions.Def_PartialMonitoringStochastic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem BanditAlgorithm.pmStoch_expected_actionSetCount_eq_selection_mass
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (S : Finset (Fin k)) : ∀ n : ℕ,
    (∫ h, ∑ t : Fin n, (if (h t).1 ∈ S then (1 : ℝ) else 0)
        ∂pmStochMeasure G π u hu n) =
      ∑ t ∈ Finset.range n,
        ∫ h, ∑ c ∈ S, (π.select t h).real {c}
          ∂pmStochMeasure G π u hu t := by
  sorry
