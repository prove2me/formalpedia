-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_positive_analytic_strip_identity_extension
-- name    : AvramDividend.Classical.avram_ws01e_b_positive_analytic_strip_identity_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:48:27.959781+00:00
-- url     : https://prove2.me/theorems/8e6f64f4-6889-46a5-ba52-906761a1c028
-- title:
--   Analytic continuation of a Wiener–Hopf transform identity from the positive moment strip
-- statement:
--   For any two real-valued functions analytic on the positive half-line, agreement on the nonempty initial interval 0<β<b implies agreement for every β>0. In the finite-rate spectrally negative Wiener–Hopf calculation, the moment argument yields equality only for β below the positive first-passage root. This theorem isolates the source-faithful analytic continuation step without assuming the unproved stochastic Wiener–Hopf factorisation or claiming that the specific transforms have already been proved analytic.
-- source:
--   Pinned Mathlib AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq and isPreconnected_Ioi (Mathlib.Analysis.Analytic.Uniqueness and Mathlib.Topology.Order.IntermediateValue); applied to the exact positive-moment-strip restriction encountered in the Kuznetsov–Kyprianou–Rivero spectrally negative Wiener–Hopf factorisation.

import Mathlib

open Set Filter
open scoped Topology

/-- Real analytic continuation of a finite-clock transform identity. -/

theorem AvramDividend.Classical.avram_ws01e_b_positive_analytic_strip_identity_extension
    (f g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hf : AnalyticOnNhd ℝ f (Ioi (0 : ℝ)))
    (hg : AnalyticOnNhd ℝ g (Ioi (0 : ℝ)))
    (hstrip : ∀ β : ℝ, 0 < β → β < b → f β = g β) :
    ∀ β : ℝ, 0 < β → f β = g β := by sorry
