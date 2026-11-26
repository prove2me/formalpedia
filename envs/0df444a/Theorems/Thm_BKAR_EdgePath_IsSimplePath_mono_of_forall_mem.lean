-- Prove2me | Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono_of_forall_mem
-- name    : BKAR.EdgePath.IsSimplePath.mono_of_forall_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:20.036895+00:00
-- url     : https://prove2.me/theorems/f4d081fb-9828-4fb1-97eb-ab7f4a6e89c5
-- title:
--   Is Simple Path: mono of forall mem
-- statement:
--   The Is Simple Path construction uses the mono of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L194-L199
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L194-L199

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
open BKAR.EdgePath.IsSimplePath

theorem BKAR.EdgePath.IsSimplePath.mono_of_forall_mem {S T : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j)
    (hmem : ∀ e ∈ γ, e ∈ T) :
    IsSimplePath T γ i j := by sorry
