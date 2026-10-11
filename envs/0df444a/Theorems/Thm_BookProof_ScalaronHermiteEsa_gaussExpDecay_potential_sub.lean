-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_potential_sub
-- name    : BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:19.979977+00:00
-- url     : https://prove2.me/theorems/424a6258-472c-4c0d-b868-78a13b3c4f86
-- title:
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) (z : ℂ) (w : L2d d) : GaussExpDecay (fun x : Vd d => (((W x : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) (z : ℂ) (w : L2d d) : GaussExpDecay (fun x : Vd d => (((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub
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
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W)
    (z : ℂ) (w : L2d d) :
    GaussExpDecay (fun x : Vd d => (((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x) := by sorry
