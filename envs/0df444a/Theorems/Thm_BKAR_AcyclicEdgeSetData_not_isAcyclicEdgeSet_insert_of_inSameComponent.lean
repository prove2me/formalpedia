-- Prove2me | Theorems.Thm_BKAR_AcyclicEdgeSetData_not_isAcyclicEdgeSet_insert_of_inSameComponent
-- name    : BKAR.AcyclicEdgeSetData.not_isAcyclicEdgeSet_insert_of_inSameComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:34.322046+00:00
-- url     : https://prove2.me/theorems/bc0eb839-29ed-5374-9b1f-bfbe31300ef5
-- title:
--   Acyclic Edge Set Data: not is Acyclic Edge Set insert of in Same Component
-- statement:
--   Adding an absent edge whose endpoints are already connected cannot preserve
--   acyclicity: the old component path and the new singleton edge would be two
--   distinct simple paths.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L393-L419
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L393-L419

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

theorem BKAR.AcyclicEdgeSetData.not_isAcyclicEdgeSet_insert_of_inSameComponent
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {e : Edge V} (heS : e ∉ S)
    (hcomp : data.inSameComponent e.left e.right) :
    ¬ IsAcyclicEdgeSet (insert e S) := by sorry
