-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
-- name    : BKAR.orderedSimplexIntegralAux_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:53.103739+00:00
-- url     : https://prove2.me/theorems/02f84de2-4c32-548f-9189-2fd15317ac84
-- title:
--   BKAR: ordered Simplex Integral Aux cons
-- statement:
--   The BKAR construction uses the ordered Simplex Integral Aux cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L53-L58
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L53-L58

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegralAux_cons (top : ℝ) (e : Edge V)
    (order : List (Edge V)) (f : List ℝ → ℝ) :
    orderedSimplexIntegralAux top (e :: order) f =
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts)) := by sorry

attribute [defeq] BKAR.orderedSimplexIntegralAux_cons
