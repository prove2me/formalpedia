-- Prove2me | Theorems.Thm_BKAR_ForestIndex_ext
-- name    : BKAR.ForestIndex.ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:32.837545+00:00
-- url     : https://prove2.me/theorems/165cad08-1944-4ebf-9a04-17bd81d3d0f5
-- title:
--   Forest Index: ext
-- statement:
--   The Forest Index construction uses the ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L454-L458
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L454-L458

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.ForestIndex
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.ForestIndex.ext {I J : ForestIndex V} (h : I.edges = J.edges) : I = J := by sorry
