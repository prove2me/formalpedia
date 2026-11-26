-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma1_im_le_norm_deriv
-- name    : ExponentialJuliaSetMisiurewicz.lemma1_im_le_norm_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:36.399716+00:00
-- url     : https://prove2.me/theorems/ab03c193-9b70-4d91-91e8-517df1b8224e
-- title:
--   Exponential Julia Set Misiurewicz: lemma1 im le norm deriv
-- statement:
--   **Lemma 1.** The imaginary part of an exponential iterate is bounded by the norm of
--   its derivative. HOL Light: `LEMMA_1`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L72-L94
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L72-L94

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.lemma1_im_le_norm_deriv {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    |(expIterate n z).im| ≤ ‖deriv (expIterate n) z‖ := by sorry
