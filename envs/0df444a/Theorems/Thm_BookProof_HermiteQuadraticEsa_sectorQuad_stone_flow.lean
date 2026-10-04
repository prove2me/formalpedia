-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_sectorQuad_stone_flow
-- name    : BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-03T11:31:54.845988+00:00
-- url     : https://prove2.me/theorems/30ca9a7e-232d-46aa-ad9d-f85274ba4e4b
-- title:
--   The Lean 4 theorem `sectorQuad_stone_flow` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sectorQuad_stone_flow` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_sectorQuadW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_sectorQuadW
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.StoneBridge
open BookProof.HermiteQuadraticEsa

variable {d : ℕ}



open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow (M alpha mu : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2)
    (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d 2)) (U : ℝ → (L2d 2 →L[ℂ] L2d 2)),
      IsSelfAdjointExtension
        (hamCore (sectorQuadW M alpha mu) (continuous_sectorQuadW M alpha mu)
          (expBounded_sectorQuadW M alpha mu)) T.op ∧ IsStoneFlow T U := by sorry
