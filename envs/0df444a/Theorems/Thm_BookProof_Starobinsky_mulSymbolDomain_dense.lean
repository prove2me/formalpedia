-- Prove2me | Theorems.Thm_BookProof_Starobinsky_mulSymbolDomain_dense
-- name    : BookProof.Starobinsky.mulSymbolDomain_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:23.96174+00:00
-- url     : https://prove2.me/theorems/de80138f-f2ca-4a2c-809c-edfafec788d4
-- title:
--   The Lean 4 theorem `mulSymbolDomain_dense` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulSymbolDomain_dense` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.mulSymbolDomain_dense
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.mulSymbolDomain_dense (lam : ℕ → ℝ) :
    Dense ((mulSymbolDomain lam : Submodule ℂ L2Nat) : Set L2Nat) := by sorry
