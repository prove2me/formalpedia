-- Prove2me | solution 1 for mme_ZMod_two_linear_hash_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:04:31.146784+00:00
-- url     : https://prove2.me/submissions/b9fd5002-b6e1-4fce-a85e-a90f822202c8

import Mathlib

open BigOperators

set_option autoImplicit false

/-- Two linear forms over `ZMod M` with a unit two-by-two minor are jointly
uniform: every pair of target values has exactly `M^n` preimages. -/
theorem solution {M n : ℕ} [NeZero M]
    (c d : Fin (n + 2) → ZMod M)
    (j k : Fin (n + 2))
    (hdet : IsUnit (c j * d k - c k * d j))
    (s t : ZMod M) :
    ((Finset.univ.filter (fun w : Fin (n + 2) → ZMod M =>
      (∑ i, c i * w i = s) ∧ (∑ i, d i * w i = t))).card) = M ^ n := by
  classical
  obtain ⟨u, hu⟩ := hdet
  let L : (Fin (n + 2) → ZMod M) →+ (ZMod M × ZMod M) :=
    { toFun := fun w => (∑ i, c i * w i, ∑ i, d i * w i)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Prod.mk_add_mk] }
  have hLsurj : Function.Surjective L := by
    intro z
    let x : ZMod M := (↑(u⁻¹) : ZMod M) * (d k * z.1 - c k * z.2)
    let y : ZMod M := (↑(u⁻¹) : ZMod M) * (c j * z.2 - d j * z.1)
    let w : Fin (n + 2) → ZMod M := Pi.single j x + Pi.single k y
    refine ⟨w, ?_⟩
    change (∑ i, c i * w i, ∑ i, d i * w i) = z
    have hfirst : c j * x + c k * y = z.1 := by
      dsimp [x, y]
      calc
        c j * (↑(u⁻¹) * (d k * z.1 - c k * z.2)) +
              c k * (↑(u⁻¹) * (c j * z.2 - d j * z.1)) =
            ↑(u⁻¹) * (c j * d k - c k * d j) * z.1 := by ring
        _ = ↑(u⁻¹) * ↑u * z.1 := by rw [hu]
        _ = z.1 := by simp
    have hsecond : d j * x + d k * y = z.2 := by
      dsimp [x, y]
      calc
        d j * (↑(u⁻¹) * (d k * z.1 - c k * z.2)) +
              d k * (↑(u⁻¹) * (c j * z.2 - d j * z.1)) =
            ↑(u⁻¹) * (c j * d k - c k * d j) * z.2 := by ring
        _ = ↑(u⁻¹) * ↑u * z.2 := by rw [hu]
        _ = z.2 := by simp
    have hsumSingle (a : Fin (n + 2) → ZMod M)
        (q : Fin (n + 2)) (r : ZMod M) :
        ∑ i, a i * Pi.single (M := fun _ => ZMod M) q r i = a q * r := by
      rw [Finset.sum_eq_single q]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    apply Prod.ext
    · change ∑ i, c i * w i = z.1
      simp only [w, Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hsumSingle, hfirst]
    · change ∑ i, d i * w i = z.2
      simp only [w, Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hsumSingle, hsecond]
  have hfiber (z : ZMod M × ZMod M) :
      (Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => L w = z)).card =
        (Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => L w = 0)).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range L
      (hLsurj z) (hLsurj 0)
  let C :=
    (Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => L w = 0)).card
  have hpartition :
      (Finset.univ : Finset (Fin (n + 2) → ZMod M)).card =
        ∑ z : ZMod M × ZMod M,
          (Finset.univ.filter
            (fun w : Fin (n + 2) → ZMod M => L w = z)).card := by
    simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, one_mul] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin (n + 2) → ZMod M)))
        (t := (Finset.univ : Finset (ZMod M × ZMod M)))
        (f := fun w => L w) (by intro q hq; simp))
  have htotal : M ^ (n + 2) = M ^ 2 * C := by
    calc
      M ^ (n + 2) = Fintype.card (Fin (n + 2) → ZMod M) := by simp
      _ = ∑ z : ZMod M × ZMod M,
          (Finset.univ.filter
            (fun w : Fin (n + 2) → ZMod M => L w = z)).card := by
              simpa using hpartition
      _ = ∑ _z : ZMod M × ZMod M, C := by
        apply Finset.sum_congr rfl
        intro z _
        exact hfiber z
      _ = M ^ 2 * C := by simp [pow_two]
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM20 : 0 < M ^ 2 := pow_pos hM0 _
  have hC : C = M ^ n := by
    rw [show M ^ (n + 2) = M ^ 2 * M ^ n by ring] at htotal
    exact Nat.eq_of_mul_eq_mul_left hM20 htotal.symm
  have htarget :
      Finset.univ.filter (fun w : Fin (n + 2) → ZMod M =>
          (∑ i, c i * w i = s) ∧ (∑ i, d i * w i = t)) =
        Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => L w = (s, t)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ((∑ i, c i * w i = s) ∧ (∑ i, d i * w i = t)) ↔
      ((∑ i, c i * w i, ∑ i, d i * w i) = (s, t))
    constructor
    · rintro ⟨hc, hd⟩
      exact Prod.ext hc hd
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  rw [htarget, hfiber (s, t)]
  exact hC
