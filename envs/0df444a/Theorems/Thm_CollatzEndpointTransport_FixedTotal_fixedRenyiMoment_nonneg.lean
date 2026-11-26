-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_nonneg
-- name    : CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:58.634303+00:00
-- url     : https://prove2.me/theorems/f565573f-28f6-5be2-9c22-f6e43cd9f23c
-- title:
--   Fixed Total: fixed Renyi Moment nonneg
-- statement:
--   The Fixed Total construction uses the fixed Renyi Moment nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L641-L645
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L641-L645

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
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralMomentCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_nonneg
    (N s : ℕ) (theta : ℝ) :
    0 ≤ fixedRenyiMoment N s theta := by sorry
