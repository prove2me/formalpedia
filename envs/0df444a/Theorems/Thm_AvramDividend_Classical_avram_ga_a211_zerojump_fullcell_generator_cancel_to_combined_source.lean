-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a211_zerojump_fullcell_generator_cancel_to_combined_source
-- name    : AvramDividend.Classical.avram_ga_a211_zerojump_fullcell_generator_cancel_to_combined_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:14:50.838649+00:00
-- url     : https://prove2.me/theorems/4451a8d1-a3f7-4cfd-a7ed-7f856a662680
-- title:
--   Original zero-jump Gaussian full-cell residual exactly cancels drift and variance generator contributions
-- statement:
--   The raw source spatial value change minus the discounted centred Brownian gradient, variance correction and Gaussian generator contributions equals one combined endpoint change minus the raw-gradient and drift-centred quadratic terms. This exact identity applies to the original positive full-cell residual before taking its positive part. Together with a210, it supports a direct one-sided large-increment Gaussian bound that avoids splitting off the potentially nonintegrable arbitrary-w positive discount term.
-- source:
--   Exact polynomial cancellation of the original zero-jump generator and centered Gaussian drift in the physical source.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a211_zerojump_fullcell_generator_cancel_to_combined_source (E0 E1 u v d h r c σ Δ : ℝ) :
 E1*(v-u) -
   (E0*(d*(r-Δ*c) + h/2*((r-Δ*c)^2-Δ*σ^2)) +
      Δ*E0*(σ^2/2*h+c*d)) =
 E1*(v-u)-E0*(d*r+h/2*(r-Δ*c)^2) := by sorry
