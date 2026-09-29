-- Prove2me | solution 1 for integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/bd85cdbd-9008-549e-89d5-09c4e355e572

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one

set_option autoImplicit false

open MeasureTheory

namespace Ws50CH3

theorem integrableOn_Ioc_piece (p q c : ℝ) (hpc : 0 < p + c) :
    IntegrableOn (fun r : ℝ => (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)) (Set.Ioc 0 1) := by
  have h1 : IntegrableOn (fun r : ℝ => r ^ (p + c - 1)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith))
  refine h1.congr_fun ?_ measurableSet_Ioc
  intro r hr
  obtain ⟨hr0, hr1⟩ := hr
  show r ^ (p + c - 1) = (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)
  rw [min_eq_right hr1, max_eq_left hr1, Real.one_rpow, mul_one, ← Real.rpow_add hr0,
    show p + (c - 1) = p + c - 1 by ring]

theorem integrableOn_Ioi_piece (p q c : ℝ) (hcq : c < q) :
    IntegrableOn (fun r : ℝ => (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)) (Set.Ioi 1) := by
  have h2 : IntegrableOn (fun r : ℝ => r ^ (c - q - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro r hr
  have hr1 : (1 : ℝ) < r := hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr1
  show r ^ (c - q - 1) = (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)
  rw [min_eq_left hr1.le, max_eq_right hr1.le, Real.one_rpow, one_mul, ← Real.rpow_add hr0,
    show -q + (c - 1) = c - q - 1 by ring]

end Ws50CH3

theorem solution
    (p q c : ℝ) (hpc : 0 < p + c) (hcq : c < q) :
    IntegrableOn (fun r : ℝ => (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (Ws50CH3.integrableOn_Ioc_piece p q c hpc).union (Ws50CH3.integrableOn_Ioi_piece p q c hcq)

end S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
end P2MW
export P2MW.S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one (solution)
