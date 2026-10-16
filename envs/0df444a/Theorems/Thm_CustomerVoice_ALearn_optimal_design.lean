-- Prove2me | Theorems.Thm_CustomerVoice_ALearn_optimal_design
-- name    : CustomerVoice.ALearn.optimal_design
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:18.949575+00:00
-- url     : https://prove2.me/theorems/fbfa2635-8d5d-425d-9b95-45b153c7f053
-- title:
--   §3.2, p. 12 — the seller's unique optimal design
-- statement:
--   For every model satisfying the standing assumptions and every possible seller belief $\hat\theta\in\{\theta_H,\theta_L\}$, the nonnegative quality
--   $$q(\hat\theta)=\frac{\gamma\hat\theta}{2s+2\gamma k}$$
--   maximizes $v(q,\hat\theta)=\gamma(\hat\theta q-kq^2)-sq^2$ over all $q\geq0$, and every nonnegative maximizer equals this quality.
--
--   This identifies the second-stage seller response used to evaluate the buyers' first-stage communication incentives.
--
--   **Formalization Note** The belief is restricted to the paper's two positive buyer types. Both attainment and uniqueness are stated; the design in an equilibrium is defined independently by maximization.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 12, §3.2, after (4)

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.ALearn

/-- §3.2, p. 12, after (4): the unique seller-optimal design for each possible belief. -/
theorem optimal_design (M : Model) (hM : M.Standing) :
    ∀ t : BType,
      (0 ≤ M.qOpt (M.θ t) ∧
        IsMaxOn (fun q : ℝ => M.v q (M.θ t)) (Set.Ici 0) (M.qOpt (M.θ t))) ∧
      ∀ q : ℝ, 0 ≤ q →
        IsMaxOn (fun r : ℝ => M.v r (M.θ t)) (Set.Ici 0) q →
          q = M.qOpt (M.θ t) := by sorry

end CustomerVoice.ALearn
