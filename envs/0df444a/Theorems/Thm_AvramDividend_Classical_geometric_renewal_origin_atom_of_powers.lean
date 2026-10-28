-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_renewal_origin_atom_of_powers
-- name    : AvramDividend.Classical.geometric_renewal_origin_atom_of_powers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:52:00.956447+00:00
-- url     : https://prove2.me/theorems/281e34a2-708b-42b2-a402-9b0ac947eab5
-- title:
--   Geometric renewal series has its sole origin atom in the zeroth term
-- statement:
--   If the initial renewal measure is a Dirac point mass at zero and every higher-order convolution power has zero mass there, the geometrically weighted renewal sum assigns exactly the initial coefficient to the singleton {0}.
-- source:
--   Measure.sum_apply_of_countable and tsum_eq_single; canonical Esscher renewal series in Avram, Palmowski and Pistorius (2007), https://arxiv.org/pdf/math/0702893.

import Theorems.Thm_AvramDividend_Classical_geometric_renewal_positive_convolution_powers_no_atom
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- A geometric sum of renewal powers carries only its initial atom at zero. -/
theorem geometric_renewal_origin_atom_of_powers
    (c : ℝ≥0∞) (m : ℕ → Measure ℝ)
    (hm0 : m 0 = Measure.dirac 0)
    (hrest : ∀ n : ℕ, 0 < n → m n ({(0 : ℝ)} : Set ℝ) = 0) :
    (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n))
      ({(0 : ℝ)} : Set ℝ) = c := by sorry

end AvramDividend.Classical
