-- Prove2me | Theorems.Thm_EulerMascheroni_P2_model_rate
-- name    : EulerMascheroni.P2.model_rate
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T00:07:56.3716+00:00
-- url     : https://prove2.me/theorems/9cbc4b0a-b157-4526-95fd-1ffae76d01db
-- title:
--   Exponential rate of the explicit fifth-root saddle models
-- statement:
--   For the explicit positive saddle models, log(fModel_(n+1)/qModel_(n+1))/scale_(n+1) tends to −c, where c=5(1−cos(2π/5)). This concerns the models themselves and makes no claim that the binomial sums have these asymptotics.
-- source:
--   Local SADDLE_DRAFT.md sections 4–5, derived from the explicit family in Van Assche–Wolfs, https://arxiv.org/html/2404.09799v3, section 5. Conditional transfer and elementary model limit, not an assertion of the full saddle asymptotics.

import Definitions.Def_eulerMascheroni_p2Approximation
open Filter Topology
open EulerMascheroni.P2

theorem EulerMascheroni.P2.model_rate :
    Tendsto (fun n : ℕ => Real.log (fModel (n+1) / qModel (n+1)) / scale (n+1))
      atTop (nhds (-rate)) := by sorry
