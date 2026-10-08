-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_continuous_scalaronPot
-- name    : BookProof.ScalaronHermiteEsa.continuous_scalaronPot
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:21.217784+00:00
-- url     : https://prove2.me/theorems/68e04e5e-379d-430f-9aa9-0b3998e1366b
-- title:
--   `BookProof.ScalaronHermiteEsa.continuous_scalaronPot` (M alpha : ℝ) : Continuous (scalaronPot M alpha)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.continuous_scalaronPot` (M alpha : ℝ) : Continuous (scalaronPot M alpha)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.continuous_scalaronPot`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.continuous_scalaronPot
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.continuous_scalaronPot (M alpha : ℝ) : Continuous (scalaronPot M alpha) := by sorry
