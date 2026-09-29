-- Prove2me | Theorems.Thm_BookProof_Starobinsky_qgR2Mode_symmetric
-- name    : BookProof.Starobinsky.qgR2Mode_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:36.727984+00:00
-- url     : https://prove2.me/theorems/9281ce72-2af7-4493-b957-5bee62eead3c
-- title:
--   The Lean 4 theorem `qgR2Mode_symmetric` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgR2Mode_symmetric` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.qgR2Mode_symmetric
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section





















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

theorem BookProof.Starobinsky.qgR2Mode_symmetric :
    SymmetricOn (mulSymbolDomain (qgModeSymbol a b (qgR2ModePotential M alpha Rc)))
      (qgR2ModeHamiltonian a b M alpha Rc) := by sorry
