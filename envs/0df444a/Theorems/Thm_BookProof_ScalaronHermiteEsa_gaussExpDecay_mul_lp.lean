-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_mul_lp
-- name    : BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:06.354549+00:00
-- url     : https://prove2.me/theorems/cf3d12ee-6130-42f9-9c5e-0ee4fff5cc43
-- title:
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp` {g : Vd d → ℂ} {C c : ℝ} (hg : AEStronglyMeasurable g (volume : Measure (Vd d))) (hbd : ∀ x, ‖g x‖ ≤ C * Real.exp (c * ‖x‖)) (w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp` {g : Vd d → ℂ} {C c : ℝ} (hg : AEStronglyMeasurable g (volume : Measure (Vd d))) (hbd : ∀ x, ‖g x‖ ≤ C * Real.exp (c * ‖x‖)) (w : L2d d) : GaussExpDecay (fun x : Vd d => g x * (w : Vd d → ℂ) x)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp
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

theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_mul_lp {g : Vd d → ℂ} {C c : ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure (Vd d)))
    (hbd : ∀ x, ‖g x‖ ≤ C * Real.exp (c * ‖x‖)) (w : L2d d) :
    GaussExpDecay (fun x : Vd d => g x * (w : Vd d → ℂ) x) := by sorry
