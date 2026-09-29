-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmonicCore_stone_flow
-- name    : BookProof.QgHermiteOscillator.harmonicCore_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:39.22744+00:00
-- url     : https://prove2.me/theorems/4edbd042-920f-46eb-acb4-e169e9f4c01c
-- title:
--   The Lean 4 theorem `harmonicCore_stone_flow` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonicCore_stone_flow` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmonicCore_stone_flow
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.QgHermiteOscillator











open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}





variable {d : ℕ}

theorem BookProof.QgHermiteOscillator.harmonicCore_stone_flow :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (harmCore (d := d)) T.op ∧ IsStoneFlow T U := by sorry
