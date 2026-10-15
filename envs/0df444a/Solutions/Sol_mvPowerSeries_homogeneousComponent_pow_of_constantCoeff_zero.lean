-- Prove2me | solution 1 for mvPowerSeries_homogeneousComponent_pow_of_constantCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:54:29.033326+00:00
-- url     : https://prove2.me/submissions/261a1aed-e8f6-479e-bc3d-fcd65baa83e3

import Mathlib.RingTheory.MvPowerSeries.Order

open scoped BigOperators

theorem solution
    {σ R : Type*} [CommSemiring R]
    (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.constantCoeff f = 0)
    (n : Nat) :
    MvPowerSeries.homogeneousComponent n (f ^ n) =
      (MvPowerSeries.homogeneousComponent 1 f) ^ n := by
  classical
  induction n with
  | zero =>
      ext d
      rw [MvPowerSeries.coeff_homogeneousComponent]
      simp only [pow_zero, MvPowerSeries.coeff_one]
      by_cases hd : Finsupp.degree d = 0
      · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd
        simp [hd0]
      · have hd0 : d ≠ 0 := by
          intro h
          subst d
          apply hd
          simp
        simp [hd, hd0]
  | succ n ih =>
      have hn : n ≤ (f ^ n).order :=
        MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hf
      have h1 : 1 ≤ f.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf
      calc
        MvPowerSeries.homogeneousComponent (n + 1) (f ^ (n + 1)) =
            MvPowerSeries.homogeneousComponent (n + 1) (f ^ n * f) := by
              rw [pow_succ]
        _ = MvPowerSeries.homogeneousComponent n (f ^ n) *
            MvPowerSeries.homogeneousComponent 1 f :=
              MvPowerSeries.homogeneousComponent_mul_of_le_order hn h1
        _ = (MvPowerSeries.homogeneousComponent 1 f) ^ n *
            MvPowerSeries.homogeneousComponent 1 f := by rw [ih]
        _ = (MvPowerSeries.homogeneousComponent 1 f) ^ (n + 1) := by
              rw [pow_succ]