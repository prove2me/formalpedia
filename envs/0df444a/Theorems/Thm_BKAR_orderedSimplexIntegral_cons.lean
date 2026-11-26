-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegral_cons
-- name    : BKAR.orderedSimplexIntegral_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:01.750937+00:00
-- url     : https://prove2.me/theorems/df0ebec9-73a1-491f-a8f5-48f68fd0886d
-- title:
--   BKAR: ordered Simplex Integral cons
-- statement:
--   The BKAR construction uses the ordered Simplex Integral cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L66-L71
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L66-L71

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegral_cons (e : Edge V) (order : List (Edge V))
    (f : List ℝ → ℝ) :
    orderedSimplexIntegral (e :: order) f =
      ∫ t in 0..(1 : ℝ),
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts)) := by sorry

attribute [defeq] BKAR.orderedSimplexIntegral_cons
