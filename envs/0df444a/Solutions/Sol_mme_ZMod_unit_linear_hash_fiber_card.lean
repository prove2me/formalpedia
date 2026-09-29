-- Prove2me | solution 1 for mme_ZMod_unit_linear_hash_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:01:32.363077+00:00
-- url     : https://prove2.me/submissions/722c513f-8dc2-4ece-9ec6-76e105e30bb8

import Mathlib

open BigOperators

set_option autoImplicit false

/-- Over an arbitrary nontrivial residue ring, a linear hash with one unit
coefficient has exactly `M^n` preimages of every value. -/
theorem solution {M n : ℕ} [NeZero M]
    (c : Fin (n + 1) → ZMod M) (j : Fin (n + 1))
    (hc : IsUnit (c j)) (s : ZMod M) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod M =>
      ∑ i, c i * w i = s)).card) = M ^ n := by
  obtain ⟨u, hu⟩ := hc
  let L : (Fin (n + 1) → ZMod M) →+ ZMod M :=
    { toFun := fun w => ∑ i, c i * w i
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have hLsurj : Function.Surjective L := by
    intro z
    let w : Fin (n + 1) → ZMod M :=
      Function.update 0 j ((↑(u⁻¹) : ZMod M) * z)
    refine ⟨w, ?_⟩
    change (∑ i, c i * w i) = z
    rw [Finset.sum_eq_single j]
    · simp [w, ← hu]
    · intro i _ hij
      simp [w, hij]
    · simp
  have hfiber (z : ZMod M) :
      (Finset.univ.filter (fun w : Fin (n + 1) → ZMod M => L w = z)).card =
        (Finset.univ.filter (fun w : Fin (n + 1) → ZMod M => L w = 0)).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range L
      (hLsurj z) (hLsurj 0)
  let C :=
    (Finset.univ.filter (fun w : Fin (n + 1) → ZMod M => L w = 0)).card
  have hpartition :
      (Finset.univ : Finset (Fin (n + 1) → ZMod M)).card =
        ∑ z : ZMod M,
          (Finset.univ.filter
            (fun w : Fin (n + 1) → ZMod M => L w = z)).card := by
    simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, one_mul] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin (n + 1) → ZMod M)))
        (t := (Finset.univ : Finset (ZMod M)))
        (f := fun w => L w) (by intro x hx; simp))
  have htotal : M ^ (n + 1) = M * C := by
    calc
      M ^ (n + 1) = Fintype.card (Fin (n + 1) → ZMod M) := by simp
      _ = ∑ z : ZMod M,
          (Finset.univ.filter
            (fun w : Fin (n + 1) → ZMod M => L w = z)).card := by
              simpa using hpartition
      _ = ∑ _z : ZMod M, C := by
        apply Finset.sum_congr rfl
        intro z _
        exact hfiber z
      _ = M * C := by simp
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hC : C = M ^ n := by
    rw [pow_succ'] at htotal
    exact Nat.eq_of_mul_eq_mul_left hM0 htotal.symm
  change (Finset.univ.filter
      (fun w : Fin (n + 1) → ZMod M => L w = s)).card = M ^ n
  rw [hfiber s]
  exact hC
