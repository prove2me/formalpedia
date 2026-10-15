-- Prove2me | solution 1 for mvPowerSeries_homogeneousComponent_finsuppProd_of_constantCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:50:03.073026+00:00
-- url     : https://prove2.me/submissions/4de31c5b-c292-4f37-841e-62c4a845ce8f

import Mathlib.RingTheory.MvPowerSeries.Order
import Theorems.Thm_mvPowerSeries_homogeneousComponent_pow_of_constantCoeff_zero
import Theorems.Thm_mvPowerSeries_homogeneousComponent_finsuppProd_of_order_le

open scoped BigOperators

theorem solution
    {σ ι R : Type*} [CommSemiring R]
    (f : ι → MvPowerSeries σ R)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (m : ι →₀ Nat) :
    MvPowerSeries.homogeneousComponent m.degree
      (m.prod (fun i k => f i ^ k)) =
    m.prod (fun i k => (MvPowerSeries.homogeneousComponent 1 (f i)) ^ k) := by
  calc
    MvPowerSeries.homogeneousComponent m.degree
        (m.prod (fun i k => f i ^ k)) =
      m.prod (fun i k => MvPowerSeries.homogeneousComponent (m i) (f i ^ m i)) := by
        exact mvPowerSeries_homogeneousComponent_finsuppProd_of_order_le
          (fun i k => f i ^ k) m (fun i => by
            simpa using MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero
              (f := f i) (m i) (hf i))
    _ = m.prod (fun i k => (MvPowerSeries.homogeneousComponent 1 (f i)) ^ k) := by
        apply Finsupp.prod_congr
        intro i hi
        exact mvPowerSeries_homogeneousComponent_pow_of_constantCoeff_zero
          (f i) (hf i) (m i)