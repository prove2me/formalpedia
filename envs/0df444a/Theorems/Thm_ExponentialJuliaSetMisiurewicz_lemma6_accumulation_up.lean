-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma6_accumulation_up
-- name    : ExponentialJuliaSetMisiurewicz.lemma6_accumulation_up
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:01.235323+00:00
-- url     : https://prove2.me/theorems/b9744ca7-9109-5242-b5b4-7e5be0d0f510
-- title:
--   Exponential Julia Set Misiurewicz: lemma6 accumulation up
-- statement:
--   **Accumulation.** If infinitely many images of `V` lie in the upper half-plane and none
--   meets the real axis, there is a finite point `p` and a centre `y` such that arbitrarily small
--   balls about `y` are carried, at arbitrarily late times, into arbitrarily small neighbourhoods
--   of `p`. This is weak Montel in the form Lemma 6 consumes.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L197-L323
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L197-L323

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.lemma6_accumulation_up
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {T : Set ℕ} (hTinf : T.Infinite)
    (hTup : ∀ n ∈ T, ∀ z ∈ V, 0 < (expIterate n z).im) :
    ∃ p y : ℂ, 0 ≤ p.im ∧
      ∀ η > 0, ∃ δ > 0, ball y δ ⊆ V ∧
        ∀ K : ℕ, ∃ n, K ≤ n ∧ ∀ z ∈ ball y δ, ‖expIterate n z - p‖ < η := by sorry
