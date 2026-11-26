-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_rpow_nat_div_rpow_nat_le_one
-- name    : CollatzEndpointTransport.FixedTotal.rpow_nat_div_rpow_nat_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:13.753289+00:00
-- url     : https://prove2.me/theorems/0278eac8-0589-4d0c-b6b1-a9a0802a3683
-- title:
--   Fixed Total: rpow nat div rpow nat le one
-- statement:
--   The Fixed Total construction uses the rpow nat div rpow nat le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L902-L907
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L902-L907

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.rpow_nat_div_rpow_nat_le_one
    {a b : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (hb : 0 < b) (hab : a ≤ b) :
    ((a : ℝ) ^ theta) / ((b : ℝ) ^ theta) ≤ 1 := by sorry
