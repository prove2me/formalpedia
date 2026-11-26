-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_lt_alpha
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiPiStar_lt_alpha
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:29.906916+00:00
-- url     : https://prove2.me/theorems/c6d3f68d-2894-4870-a0a9-e660ae2ba95a
-- title:
--   Fixed Total: central Renyi Pi Star lt alpha
-- statement:
--   The Fixed Total construction uses the central Renyi Pi Star lt alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L141-L146
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L141-L146

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiPiStar_lt_alpha
    {theta eta : ℝ}
    (heta : eta < centralRenyiAlpha theta - 1 / 2) :
    centralRenyiPiStar theta eta < centralRenyiAlpha theta := by sorry
