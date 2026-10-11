-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_norm_expGauss
-- name    : BookProof.ScalaronHermiteEsa.norm_expGauss
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:41:20.16202+00:00
-- url     : https://prove2.me/theorems/bbdbc271-b5ad-476a-8d2f-cc06224c9423
-- title:
--   `BookProof.ScalaronHermiteEsa.norm_expGauss` (c : ℝ) (x : Vd d) : ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ = Real.exp (c * ‖x‖) * gaussD x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.norm_expGauss` (c : ℝ) (x : Vd d) : ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ = Real.exp (c * ‖x‖) * gaussD x
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.norm_expGauss`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.norm_expGauss
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

theorem BookProof.ScalaronHermiteEsa.norm_expGauss (c : ℝ) (x : Vd d) :
    ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ = Real.exp (c * ‖x‖) * gaussD x := by sorry
