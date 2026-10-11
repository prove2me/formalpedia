-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_continuous_expGauss
-- name    : BookProof.ScalaronHermiteEsa.continuous_expGauss
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:40:53.228914+00:00
-- url     : https://prove2.me/theorems/0a99e5aa-57dd-4cfc-b192-47282e60841e
-- title:
--   `BookProof.ScalaronHermiteEsa.continuous_expGauss` (c : ℝ) : Continuous fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.continuous_expGauss` (c : ℝ) : Continuous fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.continuous_expGauss`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.continuous_expGauss
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

theorem BookProof.ScalaronHermiteEsa.continuous_expGauss (c : ℝ) :
    Continuous fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) := by sorry
