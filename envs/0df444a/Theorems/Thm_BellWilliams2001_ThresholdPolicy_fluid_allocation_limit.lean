-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_allocation_limit
-- name    : BellWilliams2001.ThresholdPolicy.fluid_allocation_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:31:55.920193+00:00
-- url     : https://prove2.me/theorems/ed389fed-9641-411a-9b70-79d0b9926169
-- title:
--   Lemma 8.1 — $\bar T^{r,*}\Rightarrow\bar T^*$ under the threshold policy
-- statement:
--   There is a constant $c_0>0$, depending only on the model data, such that under the threshold policies of Definition 5.1 with $c>c_0$, the fluid-scaled allocations $\bar T^{r,*}(t)=r^{-2}T^{r,*}(r^2t)$ satisfy
--   $$\bar T^{r,*}\Longrightarrow\bar T^*\qquad\text{as }r\to\infty,\qquad \bar T^*(t)=\Big(t,\ \frac{\lambda_1-\mu_1}{\mu_2}t,\ \frac{\lambda_2}{\mu_3}t\Big).$$
--
--   The threshold policy allocates the servers' time in the long-run proportions of the balanced heavy-traffic limit, which is what the formal derivation of the Brownian control problem assumes in (30).
--
--   **Formalization Note** The limit is deterministic, so weak convergence is stated as u.o.c. convergence in probability (p. 633). The threshold relations are required only for the systems with $L^r\ge1$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 633, Lemma 8.1, (97); p. 618, (29)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

namespace BellWilliams2001.ThresholdPolicy

/-- Lemma 8.1 (p. 633). There is `c₀ > 0` (depending only on the model data) such that under
the threshold policies of Definition 5.1 with any `c > c₀` (required for the systems with
`L^r ≥ 1`), the fluid-scaled allocations satisfy `T̄^{r,*} ⟹ T̄*`, with
`T̄*(t) = (t, ((λ₁ − μ₁)/μ₂) t, (λ₂/μ₃) t)` (29); the limit being deterministic, this is stated
as u.o.c. convergence in probability (p. 633). -/
theorem fluid_allocation_limit {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      UocInProb M.P (fun n ω t => M.Tbar n (Tstar n) ω t) M.fluidAllocation := by sorry

end BellWilliams2001.ThresholdPolicy
