-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_lt_one_iff
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiRatio_lt_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:43.354793+00:00
-- url     : https://prove2.me/theorems/957ab7e8-c746-5a38-bde3-ea1b46dfb346
-- title:
--   Fixed Total: central Renyi Ratio lt one iff
-- statement:
--   Exact reverse-spend critical curve.  The earlier one-way theorem is the
--   direction used by the central-window proof; this equivalence records that
--   the threshold `centralRenyiAlpha` is sharp for the geometric kernel.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L205-L215
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L205-L215

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiRatio_lt_one_iff
    {theta pi : ℝ}
    (htheta : 0 < theta) (hpi : 0 < pi) :
    centralRenyiRatio theta pi < 1 ↔
      pi < centralRenyiAlpha theta := by sorry
