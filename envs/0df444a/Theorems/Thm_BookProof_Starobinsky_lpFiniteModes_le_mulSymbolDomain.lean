-- Prove2me | Theorems.Thm_BookProof_Starobinsky_lpFiniteModes_le_mulSymbolDomain
-- name    : BookProof.Starobinsky.lpFiniteModes_le_mulSymbolDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:22.860983+00:00
-- url     : https://prove2.me/theorems/c4993ec4-fa0c-4f5b-b381-9907c5aa743c
-- title:
--   The Lean 4 theorem `lpFiniteModes_le_mulSymbolDomain` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `lpFiniteModes_le_mulSymbolDomain` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.lpFiniteModes_le_mulSymbolDomain
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.lpFiniteModes_le_mulSymbolDomain (lam : ℕ → ℝ) :
    (lpFiniteModes ℕ : Submodule ℂ L2Nat) ≤ mulSymbolDomain lam := by sorry
