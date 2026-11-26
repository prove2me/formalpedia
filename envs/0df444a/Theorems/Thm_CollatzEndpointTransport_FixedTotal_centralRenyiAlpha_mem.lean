-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_mem
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiAlpha_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:53.552843+00:00
-- url     : https://prove2.me/theorems/f0e2b3be-c5d1-4723-9feb-230495827cf6
-- title:
--   Fixed Total: central Renyi Alpha mem
-- statement:
--   The Fixed Total construction uses the central Renyi Alpha mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L119-L124
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L119-L124

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiAlpha_mem
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    centralRenyiAlpha theta ∈
      Set.Ioo (1 / 2 : ℝ) (Real.log 2 / Real.log 3) := by sorry
