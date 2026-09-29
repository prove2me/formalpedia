-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_harmonic_add_subquadratic_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:27.145892+00:00
-- url     : https://prove2.me/theorems/b7d4321e-7b3f-4fee-8e10-2dd41706bed3
-- title:
--   The Lean 4 theorem `harmonic_add_subquadratic_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonic_add_subquadratic_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_essentiallySelfAdjoint {V : Vd d → ℝ} {a b : ℝ}
    (hVc : Continuous V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (hsc : Continuous fun x => harmW x + V x) (hsb : ExpBounded fun x => harmW x + V x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (hamCore (fun x => harmW x + V x) hsc hsb) := by sorry
