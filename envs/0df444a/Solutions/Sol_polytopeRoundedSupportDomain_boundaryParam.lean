-- Prove2me | solution 1 for polytopeRoundedSupportDomain_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:10.05795+00:00
-- url     : https://prove2.me/submissions/b7f4050a-d9a9-484f-ae85-182ce4a87e48

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (polytopeRoundedSupportDomain hu hdelta hrho).boundaryParam =
      polytopeRoundedSupportCurve u delta rho := rfl
