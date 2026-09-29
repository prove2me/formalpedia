-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_harmonic_add_subquadratic_stone_flow
-- name    : BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:37.129107+00:00
-- url     : https://prove2.me/theorems/e05eb7ca-786c-42ec-a438-8f8db145258e
-- title:
--   The Lean 4 theorem `harmonic_add_subquadratic_stone_flow` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonic_add_subquadratic_stone_flow` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_stone_flow
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_stone_flow {V : Vd d → ℝ} {a b : ℝ}
    (hVc : Continuous V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (hsc : Continuous fun x => harmW x + V x) (hsb : ExpBounded fun x => harmW x + V x) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (hamCore (fun x => harmW x + V x) hsc hsb) T.op ∧ IsStoneFlow T U := by sorry
