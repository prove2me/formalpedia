-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_barrier_compare_of_attained_positive_minimal
-- name    : AvramDividend.Classical.cstar_barrier_compare_of_attained_positive_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:32:14.979668+00:00
-- url     : https://prove2.me/theorems/c5181c46-cbfc-4376-bfa3-477bca81f1a4
-- title:
--   Positive attained global scale-derivative minimum implies optimal cstar barrier comparison
-- statement:
--   For a nonnegative scale-like W whose derivative attains its positive global minimum at cstar, assume interior differentiability and endpoint continuity plus an explicit control on the extended right derivative at zero. The theorem then establishes both finiteness of cstar and dominance of the cstar barrier over every competing barrier for capital 0<=x<=cstar, deriving competitor denominator bounds from derivative minimality rather than assuming them.
-- source:
--   Compose the published cstar-finite-from-minimizer and regular-minimal barrier comparison children. The hden competitor derivative condition follows for all a>0 from the global derivative-minimizer property in cstarSet; only the a=0 extended derivative comparison must remain explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical
theorem cstar_barrier_compare_of_attained_positive_minimal
    (W : ℝ → ℝ)
    (hW : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hattain : (cstar W).toReal ∈ cstarSet W)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal)
    (hcont : ContinuousOn W (Set.Icc 0 (cstar W).toReal))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  sorry
end AvramDividend.Classical
