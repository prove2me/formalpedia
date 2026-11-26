-- Prove2me | Theorems.Thm_BKAR_Forest_activeEdgePartialSum_def
-- name    : BKAR.Forest.activeEdgePartialSum_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:13.266588+00:00
-- url     : https://prove2.me/theorems/f068b471-d3d8-597a-9061-4a9ca515ce37
-- title:
--   Forest: active Edge Partial Sum def
-- statement:
--   The Forest construction uses the active Edge Partial Sum def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L216-L221
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L216-L221

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.activeEdgePartialSum_def (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    F.activeEdgePartialSum u ρ t =
      Finset.sum F.activeEdges
        (fun e => partialDeriv e ρ (F.interpWithFill u t)) := by sorry
