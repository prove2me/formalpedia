-- Prove2me | solution 1 for scalar_tilted_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:27:35.146441+00:00
-- url     : https://prove2.me/submissions/04e8db64-b686-48c4-8254-1b3281e4dd25

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

open Set

theorem solution
    (g : ℝ → ℝ) (p fare : ℝ) (hp : 0 ≤ p)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) g)
    (hright : ∃ r, HasDerivWithinAt g r (Set.Ici p) p ∧ r ≤ fare)
    (hleft : p = 0 ∨
      ∃ l, HasDerivWithinAt g l (Set.Iic p) p ∧ fare ≤ l) :
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ p →
      g a - fare * a ≤ g b - fare * b) ∧
    (∀ a b, p ≤ a → a ≤ b →
      g b - fare * b ≤ g a - fare * a) := by
  constructor
  · intro a b ha hab hbp
    rcases eq_or_lt_of_le hab with rfl | hab
    · rfl
    rcases hleft with hpzero | ⟨l, hld, hfl⟩
    · have : a = 0 ∧ b = 0 := by constructor <;> linarith
      simp only [this.1, this.2, le_refl]
    · have hld' : HasDerivWithinAt g l (Iio p) p := hld.mono Iio_subset_Iic_self
      have hleftbound (x : ℝ) (hx : 0 ≤ x) (hxp : x < p) :
          l ≤ (g p - g x) / (p - x) := by
        simpa only [slope_def_field] using
          hconcave.le_slope_of_hasDerivWithinAt_Iio hx hp hxp hld'
      have hsl : fare ≤ (g b - g a) / (b - a) := by
        rcases eq_or_lt_of_le hbp with rfl | hbp
        · exact hfl.trans (hleftbound a ha hab)
        · exact hfl.trans ((hleftbound b (by linarith) hbp).trans
            (hconcave.slope_anti_adjacent ha hp hab hbp))
      have hmul := (le_div_iff₀ (sub_pos.mpr hab)).mp hsl
      nlinarith
  · intro a b hpa hab
    rcases eq_or_lt_of_le hab with rfl | hab
    · rfl
    rcases hright with ⟨r, hrd, hrf⟩
    have hrd' : HasDerivWithinAt g r (Ioi p) p := hrd.mono Ioi_subset_Ici_self
    have hrightbound (x : ℝ) (hpx : p < x) :
        (g x - g p) / (x - p) ≤ r := by
      simpa only [slope_def_field] using
        hconcave.slope_le_of_hasDerivWithinAt_Ioi hp (show x ∈ Ici 0 from hp.trans hpx.le) hpx hrd'
    have hsl : (g b - g a) / (b - a) ≤ fare := by
      rcases eq_or_lt_of_le hpa with rfl | hpa
      · exact (hrightbound b hab).trans hrf
      · exact (hconcave.slope_anti_adjacent hp
          (show b ∈ Ici 0 from hp.trans (hpa.le.trans hab.le)) hpa hab).trans
          ((hrightbound a hpa).trans hrf)
    have hmul := (div_le_iff₀ (sub_pos.mpr hab)).mp hsl
    nlinarith

#print axioms solution
