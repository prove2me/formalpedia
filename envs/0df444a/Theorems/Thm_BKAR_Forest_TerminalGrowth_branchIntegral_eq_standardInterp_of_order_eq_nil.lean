-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_standardInterp_of_order_eq_nil
-- name    : BKAR.Forest.TerminalGrowth.branchIntegral_eq_standardInterp_of_order_eq_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:37.906281+00:00
-- url     : https://prove2.me/theorems/bcc9fec1-20f1-4130-9d44-bc1ab23fd2fe
-- title:
--   Terminal Growth: branch Integral eq standard Interp of order eq nil
-- statement:
--   The Terminal Growth construction uses the branch Integral eq standard Interp of order eq nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L156-L160
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L156-L160

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.branchIntegral_eq_standardInterp_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = [])
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = ρ (F.standardInterp u) := by sorry
