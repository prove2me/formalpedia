-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_sectorHarmonicApprox_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-03T13:14:18.844328+00:00
-- url     : https://prove2.me/theorems/eb613654-8295-4c25-b4fd-8a55cdc44cc7
-- title:
--   The Lean 4 theorem `sectorHarmonicApprox_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sectorHarmonicApprox_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint
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

theorem BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint (M alpha : ℝ) (hM : M ≠ 0)
    (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2) (hMa : M ^ 2 < 12 * alpha) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 2))
      (hamCore (sectorQuadW M alpha (M ^ 2 / (24 * alpha)))
        (continuous_sectorQuadW M alpha (M ^ 2 / (24 * alpha)))
        (expBounded_sectorQuadW M alpha (M ^ 2 / (24 * alpha)))) := by sorry
