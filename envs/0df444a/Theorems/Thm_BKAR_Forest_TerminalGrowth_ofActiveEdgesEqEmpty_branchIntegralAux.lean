-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_ofActiveEdgesEqEmpty_branchIntegralAux
-- name    : BKAR.Forest.TerminalGrowth.ofActiveEdgesEqEmpty_branchIntegralAux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:42:43.663355+00:00
-- url     : https://prove2.me/theorems/ad2a4ce9-b984-554d-8610-62d495300dcc
-- title:
--   Terminal Growth: of Active Edges Eq Empty branch Integral Aux
-- statement:
--   The Terminal Growth construction uses the of Active Edges Eq Empty branch Integral Aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L68-L73
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L68-L73

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.ofActiveEdgesEqEmpty_branchIntegralAux
    (F : Forest V) (hF : F.activeEdges = ∅)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (ofActiveEdgesEqEmpty F hF).branchIntegralAux top u ρ =
      ρ (F.standardInterp u) := by sorry
