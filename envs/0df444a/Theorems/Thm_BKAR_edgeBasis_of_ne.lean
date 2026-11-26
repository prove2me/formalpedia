-- Prove2me | Theorems.Thm_BKAR_edgeBasis_of_ne
-- name    : BKAR.edgeBasis_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:37.551002+00:00
-- url     : https://prove2.me/theorems/64613ef8-b6a7-40a9-b17b-3cd12785c532
-- title:
--   BKAR: edge Basis of ne
-- statement:
--   The BKAR construction uses the edge Basis of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L58-L61
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L58-L61

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.edgeBasis_of_ne {e e' : Edge V} (hne : e' ≠ e) :
    edgeBasis e e' = 0 := by sorry
