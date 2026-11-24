-- Prove2me | Theorems.Thm_Erdos1219_exists_gt_of_regular
-- name    : Erdos1219.exists_gt_of_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:01.408795+00:00
-- url     : https://prove2.me/theorems/cbf0cfe6-0085-462a-a207-2ed873f92cbe
-- title:
--   Erdos1219: exists gt of regular
-- statement:
--   The Erdos1219 construction uses the exists gt of regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L39-L43
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L39-L43

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]

theorem Erdos1219.exists_gt_of_regular (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X) (x : X) :
    ∃ y, x < y := by sorry
