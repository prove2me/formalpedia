-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_moments_of_deficiency
-- name    : BookProof.ScalaronHermiteEsa.moments_of_deficiency
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:34.022682+00:00
-- url     : https://prove2.me/theorems/7edf5974-8f6c-4330-a1bc-063be9011d15
-- title:
--   `BookProof.ScalaronHermiteEsa.moments_of_deficiency` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) {z : ℂ} {w : L2d d} (hw : ∀ v : polyGaussCore (d := d), (inner ℂ (potC
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.moments_of_deficiency` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) {z : ℂ} {w : L2d d} (hw : ∀ v : polyGaussCore (d := d), (inner ℂ (potCore W hWc hWb v) (w : L2d d) : ℂ) = z * inner ℂ (v : L2d d) (w : L2d d)) (p : MvPolynomial (Fin d) ℂ) : ∫ x : Vd d, pgFun p x * ((((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.moments_of_deficiency`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.moments_of_deficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.moments_of_deficiency {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W)
    {z : ℂ} {w : L2d d}
    (hw : ∀ v : polyGaussCore (d := d),
      (inner ℂ (potCore W hWc hWb v) (w : L2d d) : ℂ) = z * inner ℂ (v : L2d d) (w : L2d d))
    (p : MvPolynomial (Fin d) ℂ) :
    ∫ x : Vd d, pgFun p x * ((((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x) = 0 := by sorry
