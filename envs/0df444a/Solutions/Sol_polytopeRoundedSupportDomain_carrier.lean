-- Prove2me | solution 1 for polytopeRoundedSupportDomain_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:47.209727+00:00
-- url     : https://prove2.me/submissions/3e77b654-b9ce-418d-8c59-e852064f77d8

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (polytopeRoundedSupportDomain hu hdelta hrho).carrier =
      smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho) := rfl
