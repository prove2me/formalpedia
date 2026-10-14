-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_pgLp_sq
-- name    : BookProof.YangMillsAbelianNoGap.norm_pgLp_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:34:33.272913+00:00
-- url     : https://prove2.me/theorems/e2e546ae-a69b-4a40-9761-c6aed8ebd1fe
-- title:
--   `BookProof.YangMillsAbelianNoGap.norm_pgLp_sq` {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) {r : ℝ} (h : gaussInt (q * q) = ((r : ℝ) : ℂ)) : ‖pgLp q‖ ^ 2 = r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianNoGap`.
--
--   `BookProof.YangMillsAbelianNoGap.norm_pgLp_sq` {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) {r : ℝ} (h : gaussInt (q * q) = ((r : ℝ) : ℂ)) : ‖pgLp q‖ ^ 2 = r
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianNoGap.norm_pgLp_sq`.

-- Generated from ChapterYangMillsAbelianNoGap.lean — theorem BookProof.YangMillsAbelianNoGap.norm_pgLp_sq
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianNoGap



open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsAbelianNoGap.norm_pgLp_sq {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) {r : ℝ}
    (h : gaussInt (q * q) = ((r : ℝ) : ℂ)) : ‖pgLp q‖ ^ 2 = r := by sorry
