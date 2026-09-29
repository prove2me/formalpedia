-- Prove2me | Theorems.Thm_BookProof_Starobinsky_confV_bddBelow
-- name    : BookProof.Starobinsky.confV_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:27:16.431501+00:00
-- url     : https://prove2.me/theorems/45b89410-9788-444a-879f-9dfeb71f9112
-- title:
--   The Lean 4 theorem `confV_bddBelow` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `confV_bddBelow` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.confV_bddBelow
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.confV_bddBelow {M alpha : ℝ} (halpha : 0 < alpha) :
    BddBelow (Set.range fun Rc => confV M alpha Rc) := by sorry
