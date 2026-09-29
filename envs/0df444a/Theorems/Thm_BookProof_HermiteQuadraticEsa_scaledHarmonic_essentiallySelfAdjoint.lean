-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_scaledHarmonic_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.scaledHarmonic_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:55.602194+00:00
-- url     : https://prove2.me/theorems/a73acba4-7c13-4fec-bfd4-bd299a319969
-- title:
--   The Lean 4 theorem `scaledHarmonic_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `scaledHarmonic_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.scaledHarmonic_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.scaledHarmonic_essentiallySelfAdjoint {lam : ℝ} (h0 : 0 < lam) (h2 : lam < 2)
    (hsc : Continuous fun x : Vd d => lam * harmW x)
    (hsb : ExpBounded fun x : Vd d => lam * harmW x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (hamCore (fun x : Vd d => lam * harmW x) hsc hsb) := by sorry
