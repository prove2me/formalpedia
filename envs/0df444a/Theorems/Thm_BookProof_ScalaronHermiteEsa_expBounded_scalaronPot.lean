-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_expBounded_scalaronPot
-- name    : BookProof.ScalaronHermiteEsa.expBounded_scalaronPot
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:49.987579+00:00
-- url     : https://prove2.me/theorems/28838e27-d218-4a49-bcd8-cd6290791d7a
-- title:
--   `BookProof.ScalaronHermiteEsa.expBounded_scalaronPot` (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronPot M alpha)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.expBounded_scalaronPot` (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronPot M alpha)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.expBounded_scalaronPot`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.expBounded_scalaronPot
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.Starobinsky
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.expBounded_scalaronPot (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronPot M alpha) := by sorry
