-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_one_add_exp_neg_four_mul_le
-- name    : CollatzEndpointTransport.Terras.one_add_exp_neg_four_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:25.833553+00:00
-- url     : https://prove2.me/theorems/f6e8691e-a44f-576c-99b8-7839eab38b1c
-- title:
--   Terras: one add exp neg four mul le
-- statement:
--   The scalar inequality behind the explicit Hoeffding optimization.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L75-L105
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L75-L105

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.one_add_exp_neg_four_mul_le (t : ℝ) :
    1 + Real.exp (-4 * t) ≤ 2 * Real.exp (-2 * t + 2 * t ^ 2) := by sorry
