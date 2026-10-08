-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationCard_natCard_orientationPreserving_flip
-- name    : BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:02:48.92667+00:00
-- url     : https://prove2.me/theorems/38bea7c9-6a36-4ff4-99af-ccf069ea7ea7
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip` (n : ℕ) : Nat.card {b : Fin (n + 1) → Bool // flipMatrix b ∈ Matrix.specialOrthogonalGroup (F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationCard`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip` (n : ℕ) : Nat.card {b : Fin (n + 1) → Bool // flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ} = 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip`.

-- Generated from ChapterFreeFieldBornSignOrientationCard.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
open BookProof.ChapterFreeFieldBornSignOrientationCard


open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation

theorem BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip (n : ℕ) :
    Nat.card {b : Fin (n + 1) → Bool //
      flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ} = 2 ^ n := by sorry
