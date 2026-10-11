-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianNoGap_idxA_lt
-- name    : BookProof.YangMillsAbelianNoGap.idxA_lt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:37:09.684312+00:00
-- url     : https://prove2.me/theorems/39dac9e0-0bda-44a9-935e-67b8dcc30086
-- title:
--   `BookProof.YangMillsAbelianNoGap.idxA_lt` (j : Fin 3) (a : Fin 8) : ((idxA j a : Fin 99) : ℕ) < 27
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianNoGap`.
--
--   `BookProof.YangMillsAbelianNoGap.idxA_lt` (j : Fin 3) (a : Fin 8) : ((idxA j a : Fin 99) : ℕ) < 27
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianNoGap.idxA_lt`.

-- Generated from ChapterYangMillsAbelianNoGap.lean — theorem BookProof.YangMillsAbelianNoGap.idxA_lt
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianNoGap



open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

theorem BookProof.YangMillsAbelianNoGap.idxA_lt (j : Fin 3) (a : Fin 8) : ((idxA j a : Fin 99) : ℕ) < 27 := by sorry
