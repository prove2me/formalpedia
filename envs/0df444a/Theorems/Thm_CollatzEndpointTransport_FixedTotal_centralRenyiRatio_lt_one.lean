-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_lt_one
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiRatio_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:29.159912+00:00
-- url     : https://prove2.me/theorems/fc801606-c8e6-5d80-b723-fd27719bcbc3
-- title:
--   Fixed Total: central Renyi Ratio lt one
-- statement:
--   Every positive proportion below `centralRenyiAlpha` gives a strictly
--   contracting reverse-spend geometric series.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L186-L200
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L186-L200

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiRatio_lt_one
    {theta pi : ℝ}
    (htheta : 0 < theta) (hpi : 0 < pi)
    (hpialpha : pi < centralRenyiAlpha theta) :
    centralRenyiRatio theta pi < 1 := by sorry
