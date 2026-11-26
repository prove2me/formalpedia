-- Prove2me | Theorems.Thm_BKAR_EdgePath_IsPath_mono_of_forall_mem
-- name    : BKAR.EdgePath.IsPath.mono_of_forall_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:13.030046+00:00
-- url     : https://prove2.me/theorems/0ebf2022-f780-4f45-98e4-4faf1ac50343
-- title:
--   Is Path: mono of forall mem
-- statement:
--   The Is Path construction uses the mono of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L129-L144
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L129-L144

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

theorem BKAR.EdgePath.IsPath.mono_of_forall_mem {S T : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j →
      (∀ e ∈ γ, e ∈ T) →
        IsPath T γ i j
  := by sorry
