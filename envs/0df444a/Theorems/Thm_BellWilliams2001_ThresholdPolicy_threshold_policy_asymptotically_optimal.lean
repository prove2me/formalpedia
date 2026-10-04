-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_policy_asymptotically_optimal
-- name    : BellWilliams2001.ThresholdPolicy.threshold_policy_asymptotically_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:35:11.507198+00:00
-- url     : https://prove2.me/theorems/5aba1fa5-9f67-406b-b479-0f1326c1b9f4
-- title:
--   Theorem 5.3 — the threshold policy is asymptotically optimal, with limiting cost $J^*$
-- statement:
--   There is a constant $c_0>0$, depending only on the model data, such that the following holds for every $c>c_0$. Let $T^{r,*}$ be the threshold policy of Definition 5.1 with $L^r=[c\log r]$, and let $J^*$ be the optimal cost (44) of the Brownian control problem. Then for every sequence $\{T^r\}$ of scheduling control policies (one for each system),
--   $$\liminf_{r\to\infty}\hat J^r(T^r)\ \ge\ J^*\ =\ \lim_{r\to\infty}\hat J^r(T^{r,*}),$$
--   and $J^*<\infty$.
--
--   No sequence of policies, including policies that anticipate the future, does asymptotically better than the Brownian control benchmark, and the threshold policies attain it: they are asymptotically optimal in the heavy-traffic limit.
--
--   **Formalization Note** $J^*$ is computed from an arbitrary pair of independent standard Brownian motions; it depends only on their law, and the statement holds for each pair. Costs take values in $[0,\infty]$. The threshold relations are required only for the systems with $L^r\ge1$, which are all but finitely many. The constant $c_0$ is chosen after the model data and before $c$, the policies and the Brownian motions.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 622, Theorem 5.3, (45); p. 621, Definition 5.1 and Remark

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

/-- Theorem 5.3 (p. 622), asymptotic optimality of the threshold policy. There is `c₀ > 0`
(depending only on the model data; Definition 5.1 and the Remark on p. 621) such that for every
`c > c₀`, every sequence `T^{r,*}` of threshold policies with threshold `L^r = [c log r]`
(required for the systems with `L^r ≥ 1`), and every pair of independent standard Brownian
motions defining `X̃` and hence `J*` (44):
* for every sequence `{T^r}` of scheduling control policies, `liminf_r Ĵ^r(T^r) ≥ J*`;
* `Ĵ^r(T^{r,*}) → J*`;
* `J* < ∞`. -/
theorem threshold_policy_asymptotically_optimal {Ω : Type*} [MeasurableSpace Ω]
    (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ),
        IsBrownianPair P' B →
        (∀ T : ℕ → Allocation Ω, (∀ n, M.IsAdmissible n (T n)) →
          M.Jstar P' B ≤ liminf (fun n => M.cost n (T n)) atTop) ∧
        Tendsto (fun n => M.cost n (Tstar n)) atTop (𝓝 (M.Jstar P' B)) ∧
        M.Jstar P' B < ⊤ := by sorry

end BellWilliams2001.ThresholdPolicy
