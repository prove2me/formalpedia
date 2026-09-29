-- Prove2me | Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
-- name    : BookProof.Starobinsky.starobinskyV_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:45.489981+00:00
-- url     : https://prove2.me/theorems/990fe988-fd8d-43b4-93c6-7d3ab36aaa72
-- title:
--   The Lean 4 theorem `starobinskyV_nonneg` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyV_nonneg` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.starobinskyV_nonneg
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.starobinskyV_nonneg {M alpha : ℝ} (halpha : 0 < alpha) (phi : ℝ) :
    0 ≤ starobinskyV M alpha phi := by sorry
