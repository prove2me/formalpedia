-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_half_lt_centralRenyiAlpha
-- name    : CollatzEndpointTransport.FixedTotal.one_half_lt_centralRenyiAlpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:19.358969+00:00
-- url     : https://prove2.me/theorems/57290d33-592e-4b62-8906-ec85674f7e35
-- title:
--   Fixed Total: one half lt central Renyi Alpha
-- statement:
--   Strict concavity places the central threshold above one half.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L63-L84
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L63-L84

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.one_half_lt_centralRenyiAlpha
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (1 / 2 : ℝ) < centralRenyiAlpha theta := by sorry
