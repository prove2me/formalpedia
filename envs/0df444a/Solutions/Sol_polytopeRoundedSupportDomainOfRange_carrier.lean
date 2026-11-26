-- Prove2me | solution 1 for polytopeRoundedSupportDomainOfRange_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:42.832789+00:00
-- url     : https://prove2.me/submissions/3d369ad9-d5fc-4d2e-83bf-f4ebe6223b81

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrange : Set.range (polytopeRoundedSupportCurve u delta rho) =
      frontier (smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho))) :
    (polytopeRoundedSupportDomainOfRange
      hu hdelta hrho hrange).carrier =
      smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho) := rfl
