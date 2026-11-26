-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_eventually_meets_centralStrip
-- name    : ExponentialJuliaSetMisiurewicz.lemma4_eventually_meets_centralStrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:59.948186+00:00
-- url     : https://prove2.me/theorems/ee947714-ff28-5046-9ec9-7462ed8037b2
-- title:
--   Exponential Julia Set Misiurewicz: lemma4 eventually meets central Strip
-- statement:
--   **Lemma 4.** Only finitely many forward images of a non-empty open connected set can
--   be disjoint from the central strip. HOL Light: `LEMMA_4`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L363-L387
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L363-L387

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.lemma4_eventually_meets_centralStrip
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, (expIterate n '' V ∩ centralStrip).Nonempty := by sorry
