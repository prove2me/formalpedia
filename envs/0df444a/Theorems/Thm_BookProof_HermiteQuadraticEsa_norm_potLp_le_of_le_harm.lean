-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_norm_potLp_le_of_le_harm
-- name    : BookProof.HermiteQuadraticEsa.norm_potLp_le_of_le_harm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:18.451158+00:00
-- url     : https://prove2.me/theorems/78073725-9f70-4fc9-a31d-415d69dd0d23
-- title:
--   The Lean 4 theorem `norm_potLp_le_of_le_harm` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_potLp_le_of_le_harm` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_potLp_le_of_le_harm
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.norm_potLp_le_of_le_harm {V : Vd d → ℝ} (hVc : Continuous V) (hVb : ExpBounded V)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (p : MvPolynomial (Fin d) ℂ) :
    ‖potLp V hVc hVb p‖ ≤ a * ‖pgLp (harmPoly * p)‖ + b * ‖pgLp p‖ := by sorry
