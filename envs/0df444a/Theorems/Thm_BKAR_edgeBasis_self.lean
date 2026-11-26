-- Prove2me | Theorems.Thm_BKAR_edgeBasis_self
-- name    : BKAR.edgeBasis_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:49.737126+00:00
-- url     : https://prove2.me/theorems/2eca90d5-e0d1-5df6-a550-f34652a11b37
-- title:
--   BKAR: edge Basis self
-- statement:
--   The BKAR construction uses the edge Basis self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L54-L56
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L54-L56

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.edgeBasis_self (e : Edge V) :
    edgeBasis e e = 1 := by sorry
