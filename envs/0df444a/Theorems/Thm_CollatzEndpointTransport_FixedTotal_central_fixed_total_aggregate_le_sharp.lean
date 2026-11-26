-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_fixed_total_aggregate_le_sharp
-- name    : CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:47:44.560539+00:00
-- url     : https://prove2.me/theorems/3bd1a1ac-41d3-4472-ba96-be737ab28852
-- title:
--   Fixed Total: central fixed total aggregate le sharp
-- statement:
--   Sharp aggregate of the central fixed-total moments.  This is the
--   `(N+1)^(1+theta)` estimate retained in the paper.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L253-L330
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L253-L330

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

theorem CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le_sharp
    {N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 3 < N)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hinterior :
      ∀ s ∈ centralLengthSet N eta, 1 < s ∧ s < N) :
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      centralMomentConstant theta eta * (N + 1 : ℝ) ^ (1 + theta) := by sorry
