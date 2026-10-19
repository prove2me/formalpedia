-- Prove2me | Theorems.Thm_BookProof_WallEsaBddBelow_constOp_symmetric
-- name    : BookProof.WallEsaBddBelow.constOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T03:31:47.720556+00:00
-- url     : https://prove2.me/theorems/17e4e381-a4f5-404c-9461-37c00192c4fa
-- title:
--   `BookProof.WallEsaBddBelow.constOp_symmetric` (c : ℝ) (x y : Lp ℂ 2 (volume : Measure ℝ)) : (inner ℂ (constOp c x) y : ℂ) = inner ℂ x (constOp c y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWallEsaBddBelow`.
--
--   `BookProof.WallEsaBddBelow.constOp_symmetric` (c : ℝ) (x y : Lp ℂ 2 (volume : Measure ℝ)) : (inner ℂ (constOp c x) y : ℂ) = inner ℂ x (constOp c y)
--
--   Formalization note: Lean 4 identifier `BookProof.WallEsaBddBelow.constOp_symmetric`.

-- Generated from ChapterWallEsaBddBelow.lean — theorem BookProof.WallEsaBddBelow.constOp_symmetric
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
open BookProof.WallEsaBddBelow



open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.WallEsaBddBelow.constOp_symmetric (c : ℝ) (x y : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (constOp c x) y : ℂ) = inner ℂ x (constOp c y) := by sorry
