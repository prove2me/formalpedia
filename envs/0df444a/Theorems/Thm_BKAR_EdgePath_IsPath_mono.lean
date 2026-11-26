-- Prove2me | Theorems.Thm_BKAR_EdgePath_IsPath_mono
-- name    : BKAR.EdgePath.IsPath.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:14.76546+00:00
-- url     : https://prove2.me/theorems/af03a825-f6b1-4dda-800d-600367db351d
-- title:
--   Is Path: mono
-- statement:
--   The Is Path construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L118-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L118-L127

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.EdgePath
variable {V} [DecidableEq V]
open BKAR.EdgePath.IsPath

theorem BKAR.EdgePath.IsPath.mono {S T : Finset (Edge V)} (hsub : S ⊆ T) :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → IsPath T γ i j
  := by sorry
