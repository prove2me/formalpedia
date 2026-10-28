-- Prove2me | solution 1 for polignac_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-25T19:14:15.095719+00:00
-- url     : https://prove2.me/submissions/34887f0a-142b-4c7a-942d-0e6852220b07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_prime_k_tuple_conjecture

theorem solution (k : ℕ) (hk : 0 < k) (hk2 : Even k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + k)}.Infinite := by
  classical
  -- The pair of offsets (0, k), as a function `Fin 2 → ℕ`.
  -- Admissibility: for every prime `p`, the residues `{0, k}` do not cover `ZMod p`.
  have hadm : ∀ p : ℕ, Nat.Prime p →
      ∃ r : ZMod p, ∀ i, (((fun i : Fin 2 => if i = 0 then 0 else k) i : ℕ) : ZMod p) ≠ r := by
    intro p hp
    by_cases hp2 : p = 2
    · -- `p = 2`: since `k` is even, both residues are `0`, so `1` is missed.
      subst hp2
      refine ⟨1, ?_⟩
      rw [Fin.forall_fin_two]
      constructor
      · show ((0 : ℕ) : ZMod 2) ≠ 1
        simp
      · show ((k : ℕ) : ZMod 2) ≠ 1
        rw [ZMod.natCast_eq_zero_iff_even.mpr hk2]
        decide
    · -- `p ≥ 3`: two residues cannot cover all of `ZMod p`.
      have hp3 : 3 ≤ p := by
        have h2 : 2 ≤ p := hp.two_le
        omega
      have : NeZero p := ⟨hp.ne_zero⟩
      have hcard : (Finset.univ.image (fun i : Fin 2 =>
          (((fun i : Fin 2 => if i = 0 then 0 else k) i : ℕ) : ZMod p))).card ≤ 2 :=
        le_trans Finset.card_image_le (by simp)
      obtain ⟨r, hr⟩ : ∃ r, r ∉ Finset.univ.image (fun i : Fin 2 =>
          (((fun i : Fin 2 => if i = 0 then 0 else k) i : ℕ) : ZMod p)) := by
        by_contra hc
        have hc' : ∀ r, r ∈ Finset.univ.image (fun i : Fin 2 =>
            (((fun i : Fin 2 => if i = 0 then 0 else k) i : ℕ) : ZMod p)) := by
          intro r
          by_contra h
          exact hc ⟨r, h⟩
        have hsub : (Finset.univ : Finset (ZMod p)) ⊆ Finset.univ.image (fun i : Fin 2 =>
            (((fun i : Fin 2 => if i = 0 then 0 else k) i : ℕ) : ZMod p)) :=
          fun x _ => hc' x
        have hle := Finset.card_le_card hsub
        rw [Finset.card_univ, ZMod.card] at hle
        omega
      exact ⟨r, fun i heq => hr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq⟩)⟩
  -- Apply the prime k-tuples conjecture to the pair `(0, k)`.
  have hinf := prime_k_tuple_conjecture 2 (fun i : Fin 2 => if i = 0 then 0 else k) hadm
  -- The resulting set of `n` is exactly the set of prime pairs at distance `k`.
  have hset : {n : ℕ | ∀ i, Nat.Prime (n + (fun i : Fin 2 => if i = 0 then 0 else k) i)} =
      {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + k)} := by
    ext n
    simp [Fin.forall_fin_two]
  rw [hset] at hinf
  exact hinf
