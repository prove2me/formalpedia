-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_confV_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T10:40:12.412931+00:00
-- url     : https://prove2.me/theorems/72065010-7328-4222-a02f-0ced9e7b253f
-- title:
--   The Lean 4 theorem `confV_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `confV_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_confW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_confW
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.HermiteQuadraticEsa

variable {d : ℕ}



open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint (M alpha : ℝ) (h0 : 0 < alpha) (h2 : alpha < 1 / 2) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 1))
      (hamCore (confW M alpha) (continuous_confW M alpha) (expBounded_confW M alpha)) := by sorry
