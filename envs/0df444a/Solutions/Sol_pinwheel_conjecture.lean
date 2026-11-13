-- Prove2me | solution 1 for pinwheel_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:44:02.658206+00:00
-- url     : https://prove2.me/submissions/3add4070-091d-4c9e-b71a-099c0633f45d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RealPinwheel_FiveSixths_Instance
import Theorems.Thm_RealPinwheel_FiveSixths_five_sixths_periodic

section
set_option autoImplicit false

namespace PinwheelConjectureDev.Real

open RealPinwheel.FiveSixths

theorem chk_pinwheel_conjecture (k : ℕ) (hk : 1 ≤ k)
    (rates : Fin k → ℕ) (hrates : ∀ i, 1 ≤ rates i)
    (hsum : ∑ i, (1 : ℚ) / rates i ≤ 5/6) :
    ∃ (schedule : ℕ → Fin k),
      ∀ i : Fin k, ∀ n : ℕ,
        ∃ m : ℕ, n ≤ m ∧ m < n + rates i ∧ schedule m = i := by
  set σ : Equiv.Perm (Fin k) := Tuple.sort rates with hσ
  have hmono : Monotone (rates ∘ σ) := Tuple.monotone_sort rates
  let A : Instance k :=
    { positive_dimension := hk
      period := fun i => (rates (σ i) : ℝ)
      one_le := fun i => by exact_mod_cast hrates (σ i)
      ordered := fun a b hab => by
        have := hmono hab
        simp only [Function.comp] at this
        show (rates (σ a) : ℝ) ≤ rates (σ b)
        exact_mod_cast this }
  have hD : density A ≤ (5 : ℝ) / 6 := by
    have h1 : density A = ∑ i, (1 : ℝ) / (rates i : ℝ) := by
      unfold density
      exact Equiv.sum_comp σ (fun i => (1 : ℝ) / (rates i : ℝ))
    rw [h1]
    have h2 : ((∑ i, (1 : ℚ) / rates i : ℚ) : ℝ) ≤ ((5 / 6 : ℚ) : ℝ) := by exact_mod_cast hsum
    push_cast at h2
    exact h2
  obtain ⟨L, S, _, _, _, hV⟩ := five_sixths_periodic A hD
  refine ⟨fun t => σ (S t), fun j n => ?_⟩
  have hc := hV (σ.symm j) 1 one_pos n
  have hceil : ⌈((1 : ℕ) : ℝ) * A.period (σ.symm j)⌉₊ = rates j := by
    simp [A]
  rw [hceil] at hc
  have hpos : 0 < ((Finset.range (rates j)).filter fun t => S (n + t) = σ.symm j).card := by
    unfold windowCount at hc; omega
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at ht
  refine ⟨n + t, by omega, by omega, ?_⟩
  simp [ht.2]

end PinwheelConjectureDev.Real
end

theorem solution : type_of% @PinwheelConjectureDev.Real.chk_pinwheel_conjecture := @PinwheelConjectureDev.Real.chk_pinwheel_conjecture
