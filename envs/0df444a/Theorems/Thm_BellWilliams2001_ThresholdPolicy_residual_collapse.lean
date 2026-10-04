-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_residual_collapse
-- name    : BellWilliams2001.ThresholdPolicy.residual_collapse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:31:48.007192+00:00
-- url     : https://prove2.me/theorems/5f89e065-cc12-4bb9-839a-0059bfda77b7
-- title:
--   Theorem 7.1 — $(\hat Q_1^r,\hat I_1^r)\Rightarrow(0,0)$ under the threshold policy
-- statement:
--   There is a constant $c_0>0$, depending only on the model data, such that if the $r$-th system operates under the threshold policy of Definition 5.1 with $L^r=[c\log r]$ and $c>c_0$, then
--   $$(\hat Q_1^r,\hat I_1^r)\Longrightarrow(\mathbf 0,\mathbf 0)\qquad\text{as }r\to\infty .$$
--
--   Under the threshold policy the diffusion-scaled class 1 queue and the diffusion-scaled idle time of server 1 vanish; this is the first half of the state-space collapse of Theorem 5.2.
--
--   **Formalization Note** The limit is deterministic, so weak convergence is stated as u.o.c. convergence in probability, $\mathbf P\big(\sup_{0\le s\le t}(|\hat Q_1^r(s)|+|\hat I_1^r(s)|)\ge\varepsilon\big)\to0$ for all $t\ge0$, $\varepsilon>0$ (the paper's equivalence, p. 633). The threshold relations are required only for the systems with $L^r\ge1$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 623, Theorem 7.1, (49); p. 633

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

namespace BellWilliams2001.ThresholdPolicy

/-- Theorem 7.1 (p. 623). There is `c₀ > 0` (depending only on the model data) such that under
the threshold policies of Definition 5.1 with any `c > c₀` (required for the systems with
`L^r ≥ 1`), `(Q̂^r_1, Î^r_1) ⟹ (0, 0)`; the limit being deterministic, this is stated as
u.o.c. convergence in probability (the paper's equivalence, p. 633). -/
theorem residual_collapse {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      UocInProb M.P
        (fun n ω t => ![M.Qhat n (Tstar n) ω t 0, M.Ihat n (Tstar n) ω t 0])
        (fun _ => 0) := by sorry

end BellWilliams2001.ThresholdPolicy
