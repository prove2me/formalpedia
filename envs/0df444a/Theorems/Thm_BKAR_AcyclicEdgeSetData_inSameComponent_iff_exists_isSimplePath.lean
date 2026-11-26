-- Prove2me | Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_iff_exists_isSimplePath
-- name    : BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:15.100301+00:00
-- url     : https://prove2.me/theorems/d1ea3049-d5e3-4147-a162-4c631119fa93
-- title:
--   Acyclic Edge Set Data: in Same Component iff exists is Simple Path
-- statement:
--   The Acyclic Edge Set Data construction uses the in Same Component iff exists is Simple Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L360-L371
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L360-L371

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.AcyclicEdgeSetData
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} :
    data.inSameComponent i j ↔
      ∃ γ : List (Edge V), EdgePath.IsSimplePath S γ i j := by sorry
