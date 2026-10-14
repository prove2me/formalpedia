-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianNoGap_vsel_idxD
-- name    : BookProof.YangMillsAbelianNoGap.vsel_idxD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:36:51.065006+00:00
-- url     : https://prove2.me/theorems/26c3abcc-9de0-4478-b826-2235438c2ed9
-- title:
--   `BookProof.YangMillsAbelianNoGap.vsel_idxD` (v₁ v₂ : ℝ) (j k : Fin 3) (a : Fin 8) : vsel v₁ v₂ (idxD j k a) = v₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianNoGap`.
--
--   `BookProof.YangMillsAbelianNoGap.vsel_idxD` (v₁ v₂ : ℝ) (j k : Fin 3) (a : Fin 8) : vsel v₁ v₂ (idxD j k a) = v₂
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianNoGap.vsel_idxD`.

-- Generated from ChapterYangMillsAbelianNoGap.lean — theorem BookProof.YangMillsAbelianNoGap.vsel_idxD
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

theorem BookProof.YangMillsAbelianNoGap.vsel_idxD (v₁ v₂ : ℝ) (j k : Fin 3) (a : Fin 8) : vsel v₁ v₂ (idxD j k a) = v₂ := by sorry
