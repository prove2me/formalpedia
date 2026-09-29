-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmonic_add_bounded_essentiallySelfAdjoint
-- name    : BookProof.QgHermiteOscillator.harmonic_add_bounded_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:53.353861+00:00
-- url     : https://prove2.me/theorems/c290f972-e0df-4463-a49c-44dcf21350e4
-- title:
--   The Lean 4 theorem `harmonic_add_bounded_essentiallySelfAdjoint` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonic_add_bounded_essentiallySelfAdjoint` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmonic_add_bounded_essentiallySelfAdjoint
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

theorem BookProof.QgHermiteOscillator.harmonic_add_bounded_essentiallySelfAdjoint {B : Vd d → ℝ} {M : ℝ}
    (hBc : Continuous B) (hM : ∀ x, |B x| ≤ M)
    (hsc : Continuous fun x => harmW x + B x) (hsb : ExpBounded fun x => harmW x + B x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (hamCore (fun x => harmW x + B x) hsc hsb) := by sorry
