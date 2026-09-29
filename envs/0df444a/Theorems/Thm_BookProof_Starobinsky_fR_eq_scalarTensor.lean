-- Prove2me | Theorems.Thm_BookProof_Starobinsky_fR_eq_scalarTensor
-- name    : BookProof.Starobinsky.fR_eq_scalarTensor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:18.408034+00:00
-- url     : https://prove2.me/theorems/448d99cb-add9-4f21-86d8-9afb5fce9878
-- title:
--   The Lean 4 theorem `fR_eq_scalarTensor` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fR_eq_scalarTensor` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.fR_eq_scalarTensor
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.fR_eq_scalarTensor {M alpha : ℝ} (hM : M ≠ 0) (halpha : alpha ≠ 0) (R : ℝ) :
    fR M alpha R
      = M ^ 2 / 2 * scalaron M alpha R * R - Upot M alpha (scalaron M alpha R) := by sorry
