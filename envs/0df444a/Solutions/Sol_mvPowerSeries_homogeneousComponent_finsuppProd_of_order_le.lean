-- Prove2me | solution 1 for mvPowerSeries_homogeneousComponent_finsuppProd_of_order_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:56:15.709853+00:00
-- url     : https://prove2.me/submissions/406a9b46-d9d9-4e13-af1c-503fb2c3ff88

import Mathlib.RingTheory.MvPowerSeries.Order

open scoped BigOperators

theorem solution
    {σ ι R : Type*} [CommSemiring R]
    (g : ι → Nat → MvPowerSeries σ R)
    (m : ι →₀ Nat)
    (hg : ∀ i, m i ≤ (g i (m i)).order) :
    MvPowerSeries.homogeneousComponent m.degree (m.prod g) =
      m.prod (fun i k => MvPowerSeries.homogeneousComponent (m i) (g i (m i))) := by
  classical
  have hunit : MvPowerSeries.homogeneousComponent 0
      (1 : MvPowerSeries σ R) = 1 := by
    ext d
    simp only [MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_one]
    by_cases hd : d = 0
    · subst d
      simp
    · simp [hd]
  have aux : ∀ s : Finset ι,
      (∀ i ∈ s, m i ≤ (g i (m i)).order) →
        MvPowerSeries.homogeneousComponent (∑ i ∈ s, m i)
            (∏ i ∈ s, g i (m i)) =
          ∏ i ∈ s, MvPowerSeries.homogeneousComponent (m i) (g i (m i)) ∧
        (∑ i ∈ s, m i) ≤ (∏ i ∈ s, g i (m i)).order := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        constructor
        · simpa using hunit
        · simp
    | @insert a s ha ih =>
        intro hs
        have hs' : ∀ i ∈ s, m i ≤ (g i (m i)).order := by
          intro i hi
          exact hs i (Finset.mem_insert_of_mem hi)
        have htail := ih hs'
        constructor
        · rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
          calc
            MvPowerSeries.homogeneousComponent
                (m a + ∑ i ∈ s, m i)
                (g a (m a) * ∏ i ∈ s, g i (m i)) =
              MvPowerSeries.homogeneousComponent (m a) (g a (m a)) *
                MvPowerSeries.homogeneousComponent
                  (∑ i ∈ s, m i) (∏ i ∈ s, g i (m i)) :=
              MvPowerSeries.homogeneousComponent_mul_of_le_order
                (hs a (Finset.mem_insert_self a s)) htail.2
            _ = MvPowerSeries.homogeneousComponent (m a) (g a (m a)) *
                ∏ i ∈ s, MvPowerSeries.homogeneousComponent (m i) (g i (m i)) := by
              rw [htail.1]
        · rw [Finset.sum_insert ha, Finset.prod_insert ha]
          calc
            ↑(m a + ∑ i ∈ s, m i) ≤
                (g a (m a)).order + (∏ i ∈ s, g i (m i)).order := by
              simpa only [ENat.natCast_add] using
                add_le_add (hs a (Finset.mem_insert_self a s)) htail.2
            _ ≤ ((g a (m a)) * ∏ i ∈ s, g i (m i)).order :=
              MvPowerSeries.order_mul_ge
  change MvPowerSeries.homogeneousComponent
      (∑ i ∈ m.support, m i) (∏ i ∈ m.support, g i (m i)) =
    ∏ i ∈ m.support, MvPowerSeries.homogeneousComponent (m i) (g i (m i))
  exact (aux m.support (fun i _ => hg i)).1