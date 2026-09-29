-- Prove2me | Theorems.Thm_BookProof_Starobinsky_qgR2Mode_deficiencyTrivialAt
-- name    : BookProof.Starobinsky.qgR2Mode_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:16.013816+00:00
-- url     : https://prove2.me/theorems/7af73498-47eb-4792-861b-bb9036a2da8d
-- title:
--   The Lean 4 theorem `qgR2Mode_deficiencyTrivialAt` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgR2Mode_deficiencyTrivialAt` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.qgR2Mode_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section





















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

theorem BookProof.Starobinsky.qgR2Mode_deficiencyTrivialAt {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (mulSymbolDomain (qgModeSymbol a b (qgR2ModePotential M alpha Rc)))
      (qgR2ModeHamiltonian a b M alpha Rc) z := by sorry
