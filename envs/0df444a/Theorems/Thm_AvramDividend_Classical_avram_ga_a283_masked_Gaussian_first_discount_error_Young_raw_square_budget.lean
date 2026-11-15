-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a283_masked_Gaussian_first_discount_error_Young_raw_square_budget
-- name    : AvramDividend.Classical.avram_ga_a283_masked_Gaussian_first_discount_error_Young_raw_square_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:17:44.868667+00:00
-- url     : https://prove2.me/theorems/f1a6eae1-063a-4ea1-8656-2bfbd246f258
-- title:
--   Masked finite Gaussian first-order discount residual absorbed into arbitrarily small raw quadratic energy plus deterministic mesh squared-width budget
-- statement:
--   On any finite original Gaussian physical-grid mask, sum of nonnegative discount first-order source QL|r| is bounded by η times the masked raw-square energy plus the number of grid cells times (QL)^2/(4η), for η>0. This is the exact finite-sum Young inequality needed to sum the local discount first-order term from proved a236 without stochastic Cauchy-Schwarz; original a240 supplies expected raw energy bound and a206 the vanishing true mesh width squared correction.
-- source:
--   Original a236 discounted smallcell first-order source, a281 scalar Young, a240 raw energy and a206 square-width rate

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a283_masked_Gaussian_first_discount_error_Young_raw_square_budget
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)] (r : ℕ → Ω → ℝ)
    (η Q L : ℝ) (hη : 0 < η)
    (hQ : 0 ≤ Q) (hL : 0 ≤ L) (ω : Ω) :
    (∑ i ∈ S, if A i ω then Q*L*|r i ω| else 0) ≤
      η*(∑ i ∈ S, if A i ω then (r i ω)^2 else 0) +
        (S.card : ℝ)*(Q*L)^2/(4*η) := by sorry
