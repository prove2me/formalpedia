-- Prove2me | Theorems.Thm_BookProof_Starobinsky_starobinskyV_tendsto_atBot_atTop
-- name    : BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:58.286979+00:00
-- url     : https://prove2.me/theorems/f3ed5f14-9fc2-4b39-878c-1593d3ed711f
-- title:
--   The Lean 4 theorem `starobinskyV_tendsto_atBot_atTop` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyV_tendsto_atBot_atTop` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) :
    Tendsto (fun phi => starobinskyV M alpha phi) atBot atTop := by sorry
