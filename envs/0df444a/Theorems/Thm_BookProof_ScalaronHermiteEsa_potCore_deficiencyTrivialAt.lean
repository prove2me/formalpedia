-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_potCore_deficiencyTrivialAt
-- name    : BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:44:18.38896+00:00
-- url     : https://prove2.me/theorems/eee87690-3067-4ec0-b80e-9866245643c4
-- title:
--   `BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (potCore W hWc hWb) z
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.QgHermiteOscillator
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (potCore W hWc hWb) z := by sorry
