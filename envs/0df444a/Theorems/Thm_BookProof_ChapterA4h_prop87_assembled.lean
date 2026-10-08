-- Prove2me | Theorems.Thm_BookProof_ChapterA4h_prop87_assembled
-- name    : BookProof.ChapterA4h.prop87_assembled
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:54.87048+00:00
-- url     : https://prove2.me/theorems/d395e839-9057-44f4-a96c-d89bc5574eab
-- title:
--   `BookProof.ChapterA4h.prop87_assembled` (Mk : MackeyImprimitivity R) (Wg : WignerClassification R Mk) (ρ : R) : PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4h`.
--
--   `BookProof.ChapterA4h.prop87_assembled` (Mk : MackeyImprimitivity R) (Wg : WignerClassification R Mk) (ρ : R) : PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive ∨ PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.masslessDiscrete
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4h.prop87_assembled`.

-- Generated from ChapterA4h.lean — theorem BookProof.ChapterA4h.prop87_assembled
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4h
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.WeylCauchyRiemann
open BookProof.ChapterA4h


open Matrix


open BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5

variable (R : Type*)

theorem BookProof.ChapterA4h.prop87_assembled (Mk : MackeyImprimitivity R)
    (Wg : WignerClassification R Mk) (ρ : R) :
    PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive ∨
    PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.masslessDiscrete := by sorry
