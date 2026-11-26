-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_pos
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiPiStar_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:41.298571+00:00
-- url     : https://prove2.me/theorems/4142f2b4-71c4-41f1-bfbe-275adeee1954
-- title:
--   Fixed Total: central Renyi Pi Star pos
-- statement:
--   The Fixed Total construction uses the central Renyi Pi Star pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L255-L261
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L255-L261

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiPiStar_pos
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiPiStar theta eta := by sorry
