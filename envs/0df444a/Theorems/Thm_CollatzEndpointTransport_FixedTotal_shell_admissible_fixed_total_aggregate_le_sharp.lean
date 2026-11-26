-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_shell_admissible_fixed_total_aggregate_le_sharp
-- name    : CollatzEndpointTransport.FixedTotal.shell_admissible_fixed_total_aggregate_le_sharp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:10.662195+00:00
-- url     : https://prove2.me/theorems/5b311277-26f5-4f0f-96cb-414b69035645
-- title:
--   Fixed Total: shell admissible fixed total aggregate le sharp
-- statement:
--   Sharp aggregate for the lengths that are actually admissible in one
--   first-odd cohort.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L641-L698
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L641-L698

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.shell_admissible_fixed_total_aggregate_le_sharp
    {M N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 0 < N) :
    (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      centralMomentConstant theta eta * (N + 1 : ℝ) *
        (M + 1 : ℝ) ^ theta := by sorry
