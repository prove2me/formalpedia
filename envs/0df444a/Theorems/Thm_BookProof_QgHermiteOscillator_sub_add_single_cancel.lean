-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_sub_add_single_cancel
-- name    : BookProof.QgHermiteOscillator.sub_add_single_cancel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:54.661865+00:00
-- url     : https://prove2.me/theorems/f1d80193-9a85-45f1-adaa-d2cb41722c64
-- title:
--   The Lean 4 theorem `sub_add_single_cancel` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sub_add_single_cancel` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.sub_add_single_cancel
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

theorem BookProof.QgHermiteOscillator.sub_add_single_cancel {i : Fin d} {a : Fin d →₀ ℕ} (h : 1 ≤ a i) :
    (a - Finsupp.single i 1) + Finsupp.single i 1 = a := by sorry
