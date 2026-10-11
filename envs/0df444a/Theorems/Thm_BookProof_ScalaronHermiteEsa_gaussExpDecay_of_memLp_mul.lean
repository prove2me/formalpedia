-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_of_memLp_mul
-- name    : BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:41:29.489728+00:00
-- url     : https://prove2.me/theorems/7827def9-d14d-4646-b3cc-d6b448be25c0
-- title:
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul` {u w : Vd d → ℂ} {C c : ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Vd d))) (hw : MemLp w 2 (volume : Measure (Vd d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul` {u w : Vd d → ℂ} {C c : ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Vd d))) (hw : MemLp w 2 (volume : Measure (Vd d))) (hbd : ∀ x, ‖u x‖ ≤ C * Real.exp (c * ‖x‖) * ‖w x‖) : GaussExpDecay u
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul
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
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteCore
open BookProof.HermiteProductCore
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul {u w : Vd d → ℂ} {C c : ℝ}
    (hu : AEStronglyMeasurable u (volume : Measure (Vd d)))
    (hw : MemLp w 2 (volume : Measure (Vd d)))
    (hbd : ∀ x, ‖u x‖ ≤ C * Real.exp (c * ‖x‖) * ‖w x‖) :
    GaussExpDecay u := by sorry
