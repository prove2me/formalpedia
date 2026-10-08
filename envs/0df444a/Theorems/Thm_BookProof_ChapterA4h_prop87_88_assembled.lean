-- Prove2me | Theorems.Thm_BookProof_ChapterA4h_prop87_88_assembled
-- name    : BookProof.ChapterA4h.prop87_88_assembled
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:49:18.399019+00:00
-- url     : https://prove2.me/theorems/81669b27-7a7c-45ea-b004-a8ea494af827
-- title:
--   `BookProof.ChapterA4h.prop87_88_assembled` (Mk : MackeyImprimitivity R) (Wg : WignerClassification R Mk) (ρ : R) : (PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.mas
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4h`.
--
--   `BookProof.ChapterA4h.prop87_88_assembled` (Mk : MackeyImprimitivity R) (Wg : WignerClassification R Mk) (ρ : R) : (PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive ∨ PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.masslessDiscrete) ∧ ¬ ∀ j : Fin 3, projPos * spatialOp j = spatialOp j * projPos
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4h.prop87_88_assembled`.

-- Generated from ChapterA4h.lean — theorem BookProof.ChapterA4h.prop87_88_assembled
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4h
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.ChapterA4e
open BookProof.WeylCauchyRiemann
open BookProof.ChapterA4h


open Matrix


open BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5

variable (R : Type*)

theorem BookProof.ChapterA4h.prop87_88_assembled (Mk : MackeyImprimitivity R)
    (Wg : WignerClassification R Mk) (ρ : R) :
    (PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive ∨
      PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.masslessDiscrete) ∧
    ¬ ∀ j : Fin 3, projPos * spatialOp j = spatialOp j * projPos := by sorry
