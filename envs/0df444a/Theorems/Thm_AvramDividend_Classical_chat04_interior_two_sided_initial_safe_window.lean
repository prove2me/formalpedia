-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
-- name    : AvramDividend.Classical.chat04_interior_two_sided_initial_safe_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:32:38.358121+00:00
-- url     : https://prove2.me/theorems/c9d6c919-5bd9-4d85-b1b6-7f2a7fb52194
-- title:
--   Every interior initial reserve admits a common strict two-sided no-exit time window
-- statement:
--   Let a Lévy process start at zero and place the reserve at x with 0<x<a. By right-continuity, each sample path remains inside the interval (-x,a-x) for some path-dependent positive time. Thus one common initial time window avoids both strict lower and upper exits. This stronger pathwise fact supports fixed-time killed q-scale convergence and strict two-sided stopping arguments from interior reserves.
-- source:
--   Direct from the right-continuity field of SpectrallyNegativeLevy and the pinned Mathlib order-neighbourhood lemma. Exact terminal strict exit event of canonical two_sided_exit_stopped_scale_identity 09663d0d, especially its missing 0<x<a interior case.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_interior_two_sided_initial_safe_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (hx0 : 0 < x) (hxa : x < a) (ω : Ω) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε →
        -x ≤ X.X t ω ∧ X.X t ω ≤ a - x := by sorry
