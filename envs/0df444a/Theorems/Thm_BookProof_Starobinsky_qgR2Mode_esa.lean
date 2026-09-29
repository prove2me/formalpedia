-- Prove2me | Theorems.Thm_BookProof_Starobinsky_qgR2Mode_esa
-- name    : BookProof.Starobinsky.qgR2Mode_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:25.966836+00:00
-- url     : https://prove2.me/theorems/ae783c70-078a-4858-a808-98798c4139d1
-- title:
--   The Lean 4 theorem `qgR2Mode_esa` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgR2Mode_esa` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.qgR2Mode_esa
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section





















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

theorem BookProof.Starobinsky.qgR2Mode_esa :
    EssentiallySelfAdjointOn
      (mulSymbolDomain (qgModeSymbol a b (qgR2ModePotential M alpha Rc)))
      (qgR2ModeHamiltonian a b M alpha Rc) := by sorry
