-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
-- name    : BKAR.Forest.OrderedGrowth.params_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:34.838215+00:00
-- url     : https://prove2.me/theorems/1086dc5f-3d06-49bf-aa1b-6db4ac27d1f1
-- title:
--   Ordered Growth: params nil
-- statement:
--   The Ordered Growth construction uses the params nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L65-L67
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L65-L67

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_nil (F : Forest V) (u : F.EdgeParam → ℝ) (ts : List ℝ) :
    (OrderedGrowth.nil F).params u ts = u := by sorry

attribute [defeq] BKAR.Forest.OrderedGrowth.params_nil
