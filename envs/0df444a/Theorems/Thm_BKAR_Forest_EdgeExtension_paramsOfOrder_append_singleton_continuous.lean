-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_paramsOfOrder_append_singleton_continuous
-- name    : BKAR.Forest.EdgeExtension.paramsOfOrder_append_singleton_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:04:11.796939+00:00
-- url     : https://prove2.me/theorems/dd920d8a-655e-491a-80cc-23ad57037580
-- title:
--   Edge Extension: params Of Order append singleton continuous
-- statement:
--   The Edge Extension construction uses the params Of Order append singleton continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean#L32-L48
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean#L32-L48

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_CubePartition_Smoothness
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}

theorem BKAR.Forest.EdgeExtension.paramsOfOrder_append_singleton_continuous
    (h : EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    Continuous
      (fun t : ℝ =>
        F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t])) := by sorry
