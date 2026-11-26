-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_standardInterp_of_order_eq_nil
-- name    : BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_standardInterp_of_order_eq_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:43:14.54262+00:00
-- url     : https://prove2.me/theorems/8233fd2c-2cff-46de-a159-61ef5e48bfd4
-- title:
--   Terminal Growth: branch Integral Aux eq standard Interp of order eq nil
-- statement:
--   The branch integral of a terminal growth with empty order is just evaluation at
--   the initial standard interpolation point.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L145-L154
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L145-L154

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_standardInterp_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ = ρ (F.standardInterp u) := by sorry
