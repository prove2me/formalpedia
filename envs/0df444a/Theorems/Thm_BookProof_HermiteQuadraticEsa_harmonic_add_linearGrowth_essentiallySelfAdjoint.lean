-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_harmonic_add_linearGrowth_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.harmonic_add_linearGrowth_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:33:03.506892+00:00
-- url     : https://prove2.me/theorems/cf19d982-7668-4a78-b014-447f6a46375b
-- title:
--   The Lean 4 theorem `harmonic_add_linearGrowth_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonic_add_linearGrowth_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.harmonic_add_linearGrowth_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.harmonic_add_linearGrowth_essentiallySelfAdjoint {V : Vd d → ℝ} {Ccoef B : ℝ}
    (hB : 0 ≤ B)
    (hV : ∀ x, |V x| ≤ Ccoef * ‖x‖ + B)
    (hsc : Continuous fun x => harmW x + V x) (hsb : ExpBounded fun x => harmW x + V x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (hamCore (fun x => harmW x + V x) hsc hsb) := by sorry
