-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_sectorQuad_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.sectorQuad_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-03T10:40:54.163508+00:00
-- url     : https://prove2.me/theorems/737919ec-6475-4f26-95e8-d02f42cec56d
-- title:
--   The Lean 4 theorem `sectorQuad_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sectorQuad_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.sectorQuad_essentiallySelfAdjoint
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
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_sectorQuadW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_sectorQuadW
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.HermiteQuadraticEsa

variable {d : ℕ}



open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.HermiteQuadraticEsa.sectorQuad_essentiallySelfAdjoint (M alpha mu : ℝ) (ha0 : 0 < alpha)
    (ha2 : alpha < 1 / 2) (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 2))
      (hamCore (sectorQuadW M alpha mu) (continuous_sectorQuadW M alpha mu)
        (expBounded_sectorQuadW M alpha mu)) := by sorry
