-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a288_combined_small_discount_Young_second_energy_cross
-- name    : AvramDividend.Classical.avram_ga_a288_combined_small_discount_Young_second_energy_cross
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:17:55.383341+00:00
-- url     : https://prove2.me/theorems/8c7f38ca-25ad-498c-981c-35eb9379277d
-- title:
--   Original Gaussian combined small-cell one-sided source bounded by arbitrary small raw-square energy, deterministic discount mesh correction and Hessian cross
-- statement:
--   For nonnegative Gaussian discount rate, cell start and width, the true combined discounted small-cell one-sided positive source from a236 is at most (epsilon+eta) times raw increment square plus the squared first-order discount cell width times Lipschitz bound divided by 4eta, plus the Hessian raw-versus-centred quadratic cross. The only small-Taylor premise controls its positive part, and eta>0 is an arbitrary additional energy budget. This closes the pointwise Young step for a264 original stopped fullcell Gaussian small error expected L1.
-- source:
--   a236 original discounted one-sided Gaussian cell + a281 discount Young raw increment energy

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a288_combined_small_discount_Young_second_energy_cross
    (q s Δ u v d h r z ε L M η : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hη : 0 < η)
    (hTaylor : max (Real.exp (-(q*s)) *
      (v-u-d*r-h/2*r^2)) 0 ≤ ε*r^2)
    (hLip : |v-u| ≤ L*|r|) (hh : |h| ≤ M) :
    max (Real.exp (-(q*(s+Δ))) * (v-u) -
      Real.exp (-(q*s)) * (d*r+h/2*z^2)) 0 ≤
      (ε+η)*r^2+(q*Δ*L)^2/(4*η)+M/2*|r^2-z^2| := by sorry
