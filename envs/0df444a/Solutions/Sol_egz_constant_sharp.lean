-- Prove2me | solution 1 for egz_constant_sharp
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:47:20.899989+00:00
-- url     : https://prove2.me/submissions/4d096001-d961-4951-a691-1e509c6d043b

import Mathlib

/-!
**Sharpness of the Erdős–Ginzburg–Ziv theorem.** The constant `2n - 1` cannot be improved:
among `2n - 2` integers — `n - 1` zeros and `n - 1` ones — no `n` of them have a sum
divisible by `n` (for `n ≥ 2`). Any chosen `n` have sum equal to the number of chosen
ones, which lies in `[0, n - 1]` and is divisible by `n` only when it is `0`, forcing all
`n` chosen elements to be zeros — of which there are only `n - 1`.
-/

open Finset

/-- The Erdős–Ginzburg–Ziv constant `2n - 1` is best possible. -/
theorem solution (n : ℕ) (hn : 1 < n) :
    ∃ a : Fin (2 * n - 2) → ℤ, ∀ t : Finset (Fin (2 * n - 2)), t.card = n →
      ¬ ((n : ℤ) ∣ ∑ i ∈ t, a i) := by
  classical
  -- indices `[0, n-1)` carry the value `1`; indices `[n-1, 2n-2)` carry `0`
  refine ⟨fun i => if (i : ℕ) < n - 1 then 1 else 0, fun t htc hdvd => ?_⟩
  -- the sum is exactly the number of selected ones
  have hsum : ∑ i ∈ t, (if (i : ℕ) < n - 1 then (1 : ℤ) else 0)
      = (((t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).card : ℕ) : ℤ) := by
    have h1 : ∑ i ∈ t, (if (i : ℕ) < n - 1 then (1 : ℤ) else 0)
        = ∑ i ∈ t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1), (1 : ℤ) := by
      rw [Finset.sum_filter]
    rw [h1]
    simp [Finset.sum_const]
  -- at most `n - 1` ones can be selected
  have hselle : (t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).card ≤ n - 1 := by
    have h1 : (t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).image Fin.val
        ⊆ Finset.range (n - 1) := by
      intro k hk
      rw [mem_image] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      rw [mem_filter] at hi
      rw [mem_range]
      exact hi.2
    have h3 : ((t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).image Fin.val).card
        = (t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have h2 := Finset.card_le_card h1
    rw [h3, Finset.card_range] at h2
    exact h2
  rw [hsum] at hdvd
  have hdvd' : n ∣ (t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).card := by
    have h1 := Int.natCast_dvd.mp hdvd
    rwa [Int.natAbs_natCast] at h1
  obtain ⟨c, hc⟩ := hdvd'
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · -- sum zero: no ones were selected, so all `n` chosen indices lie in the zeros block
    have hempty : t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1) = ∅ := Finset.card_eq_zero.mp hc
    have hinj : ∀ i ∈ t, n - 1 ≤ (i : ℕ) := by
      intro i hi
      by_contra hilt
      have hmem : i ∈ t.filter (fun j : Fin (2 * n - 2) => (j : ℕ) < n - 1) :=
        Finset.mem_filter.2 ⟨hi, lt_of_not_ge hilt⟩
      rw [hempty] at hmem
      exact absurd hmem (by simp)
    -- translating the zeros block down by `n - 1` injects `t` into `range (n - 1)`
    have hsub : (t.image (fun i : Fin (2 * n - 2) => (i : ℕ) - (n - 1)))
        ⊆ Finset.range (n - 1) := by
      intro k hk
      rw [mem_image] at hk
      obtain ⟨i, hi, hik⟩ := hk
      have hilt : (i : ℕ) < 2 * n - 2 := i.isLt
      rw [mem_range]
      omega
    have hcardmap : (t.image (fun i : Fin (2 * n - 2) => (i : ℕ) - (n - 1))).card = t.card := by
      refine Finset.card_image_of_injOn (fun a ha b hb hab => ?_)
      have h1 := hinj a ha
      have h2 := hinj b hb
      exact Fin.ext (by omega)
    have h2 := Finset.card_le_card hsub
    rw [hcardmap, Finset.card_range] at h2
    omega
  · -- at least `n` ones were selected, but only `n - 1` exist
    have hbig : n ≤ (t.filter (fun i : Fin (2 * n - 2) => (i : ℕ) < n - 1)).card := by
      rw [hc]
      calc n = n * 1 := by ring
        _ ≤ n * c := Nat.mul_le_mul le_rfl hc0
    omega
