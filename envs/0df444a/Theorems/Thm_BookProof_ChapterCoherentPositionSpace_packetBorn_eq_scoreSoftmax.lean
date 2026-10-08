-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentPositionSpace_packetBorn_eq_scoreSoftmax
-- name    : BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:04:58.353395+00:00
-- url     : https://prove2.me/theorems/a6864f47-f884-4fdf-afa0-bfe365c686f5
-- title:
--   `BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax` {m : ℕ} (q : ℝ) (k : Fin m → ℝ) (j : Fin m) : packetBorn q k j = scoreSoftmax (1 / 2) (fun l => -(q - k l) ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentPositionSpace`.
--
--   `BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax` {m : ℕ} (q : ℝ) (k : Fin m → ℝ) (j : Fin m) : packetBorn q k j = scoreSoftmax (1 / 2) (fun l => -(q - k l) ^ 2) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax`.

-- Generated from ChapterCoherentPositionSpace.lean — theorem BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterCoherentPositionSpace


open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

theorem BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax {m : ℕ} (q : ℝ) (k : Fin m → ℝ) (j : Fin m) :
    packetBorn q k j = scoreSoftmax (1 / 2) (fun l => -(q - k l) ^ 2) j := by sorry
