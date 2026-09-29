-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_of_le_harm
-- name    : BookProof.HermiteQuadraticEsa.expBounded_of_le_harm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:43.730229+00:00
-- url     : https://prove2.me/theorems/0bb43034-7a90-4f1f-abef-6fdce5421b5d
-- title:
--   The Lean 4 theorem `expBounded_of_le_harm` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `expBounded_of_le_harm` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_of_le_harm
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.expBounded_of_le_harm {V : Vd d → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) : ExpBounded V := by sorry
