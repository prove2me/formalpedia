-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_fourier_gaussD_mul_eq_zero_of_gaussExpDecay
-- name    : BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:30.043976+00:00
-- url     : https://prove2.me/theorems/b903f72c-d03a-43de-8709-f02889686526
-- title:
--   `BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay` {u : Vd d → ℂ} (hu : GaussExpDecay u) (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay` {u : Vd d → ℂ} (hu : GaussExpDecay u) (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) (w : Vd d) : 𝓕 (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) w = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay {u : Vd d → ℂ} (hu : GaussExpDecay u)
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) (w : Vd d) :
    𝓕 (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) w = 0 := by sorry
