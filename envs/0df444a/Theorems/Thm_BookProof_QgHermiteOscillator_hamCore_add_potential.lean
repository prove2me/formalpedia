-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_hamCore_add_potential
-- name    : BookProof.QgHermiteOscillator.hamCore_add_potential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:56.643984+00:00
-- url     : https://prove2.me/theorems/f9fd3b64-01f0-4515-baac-a6373579d279
-- title:
--   The Lean 4 theorem `hamCore_add_potential` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hamCore_add_potential` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.hamCore_add_potential
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

theorem BookProof.QgHermiteOscillator.hamCore_add_potential (V W : Vd d → ℝ) (hVc : Continuous V) (hVb : ExpBounded V)
    (hWc : Continuous W) (hWb : ExpBounded W)
    (hsc : Continuous fun x => V x + W x) (hsb : ExpBounded fun x => V x + W x) :
    hamCore (fun x => V x + W x) hsc hsb = hamCore V hVc hVb + potCore W hWc hWb := by sorry
