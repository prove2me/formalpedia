-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
-- name    : AvramDividend.Classical.avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:04:25.030198+00:00
-- url     : https://prove2.me/theorems/7240d1dc-0544-4b9c-bda0-c7639b4af42f
-- title:
--   Original Gaussian physical discount combined small-cell positive residual from one-sided Taylor, local Lipschitz and cross energy
-- statement:
--   For nonnegative original discount q, physical cell time and width, the positive combined discounted source error is at most the one-sided positive Taylor remainder epsilon r squared, plus a q times width local Lipschitz first-order term and the Hessian raw-versus-centred quadratic cross. The hypotheses exactly match proved original source small Taylor a194 and local C² controls, and the conclusion is the one-step analytical estimate used to close original combined Gaussian a216.
-- source:
--   a234 one-sided Gaussian Taylor discount cross and a235 original exponential discount cell width

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
    (q s Δ u v d h r z ε L M : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hTaylor : max (Real.exp (-(q*s)) *
      (v-u-d*r-h/2*r^2)) 0 ≤ ε*r^2)
    (hLip : |v-u| ≤ L*|r|) (hh : |h| ≤ M) :
    max (Real.exp (-(q*(s+Δ))) * (v-u) -
      Real.exp (-(q*s)) * (d*r+h/2*z^2)) 0 ≤
      ε*r^2 + (q*Δ)*L*|r| + M/2*|r^2-z^2| := by sorry
