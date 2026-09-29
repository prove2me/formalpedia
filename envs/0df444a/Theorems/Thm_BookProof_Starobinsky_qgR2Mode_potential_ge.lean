-- Prove2me | Theorems.Thm_BookProof_Starobinsky_qgR2Mode_potential_ge
-- name    : BookProof.Starobinsky.qgR2Mode_potential_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:27:27.557069+00:00
-- url     : https://prove2.me/theorems/9b3b7ede-df40-42b9-abbd-029884b32daa
-- title:
--   The Lean 4 theorem `qgR2Mode_potential_ge` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgR2Mode_potential_ge` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.qgR2Mode_potential_ge
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section





















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

theorem BookProof.Starobinsky.qgR2Mode_potential_ge (halpha : 0 < alpha) (k : ℕ) :
    -(M ^ 4 / (16 * alpha)) ≤ qgR2ModePotential M alpha Rc k := by sorry
