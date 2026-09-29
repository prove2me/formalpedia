-- Prove2me | solution 1 for mme_ZMod_unit_affine_collision_parameter_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:20:18.91505+00:00
-- url     : https://prove2.me/submissions/4f7c8510-80fb-4d81-a5c2-cfdd9238d7f9

import Mathlib
import Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card

open BigOperators

set_option autoImplicit false

/-- A unit-coefficient linear collision equation together with a uniquely
determined affine offset leaves at most `M^n` parameter pairs. -/
theorem solution {M n : ℕ} [NeZero M]
    (c : Fin (n + 1) → ZMod M) (j : Fin (n + 1))
    (hc : IsUnit (c j))
    (offset : (Fin (n + 1) → ZMod M) → ZMod M)
    (P : ((Fin (n + 1) → ZMod M) × ZMod M) → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod M) × ZMod M =>
        (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1 ∧ P q)).card) ≤
      M ^ n := by
  let A := Finset.univ.filter
    (fun q : (Fin (n + 1) → ZMod M) × ZMod M =>
      (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1 ∧ P q)
  let B := Finset.univ.filter
    (fun w : Fin (n + 1) → ZMod M => (∑ i, c i * w i) = 0)
  have hinj : Set.InjOn
      (fun q : (Fin (n + 1) → ZMod M) × ZMod M => q.1)
      (↑A : Set ((Fin (n + 1) → ZMod M) × ZMod M)) := by
    rintro ⟨w, b⟩ hwb ⟨w', b'⟩ hwb' hww'
    simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hwb hwb'
    change w = w' at hww'
    subst w'
    exact congrArg (fun z => (w, z))
      (hwb.2.1.trans hwb'.2.1.symm)
  have himage : A.image
      (fun q : (Fin (n + 1) → ZMod M) × ZMod M => q.1) ⊆ B := by
    intro w hw
    obtain ⟨q, hqA, rfl⟩ := Finset.mem_image.mp hw
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp hqA).2.1
  calc
    A.card = (A.image
        (fun q : (Fin (n + 1) → ZMod M) × ZMod M => q.1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ B.card := Finset.card_le_card himage
    _ = M ^ n := mme_ZMod_unit_linear_hash_fiber_card c j hc 0
