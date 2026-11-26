-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiNumerator_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedRenyiNumerator_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:57.43339+00:00
-- url     : https://prove2.me/theorems/bc53a0f3-0866-40d4-8ab2-680cfd3debdb
-- title:
--   Fixed Total: fixed Renyi Numerator le
-- statement:
--   The Fixed Total construction uses the fixed Renyi Numerator le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L618-L628
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L618-L628

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

theorem CollatzEndpointTransport.FixedTotal.fixedRenyiNumerator_le
    (N s : ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    fixedRenyiNumerator N s theta ≤
      4 * fixedLiftMoment N s theta := by sorry
