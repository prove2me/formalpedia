-- Prove2me | solution 1 for finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:09.836298+00:00
-- url     : https://prove2.me/submissions/c55d6118-1515-4061-aeea-df0e476a35f4

import Mathlib
import Theorems.Thm_finite_three_injective_fixed_point_free_iterate_transitive_aux__p2m_c087dd6c_81e7_4e4c_ad72_7053d1a189f4_a1

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (f : α → α) (P : α → Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : ∀ x, P x → P (f x))
    (hinj : Function.Injective f) (hfixed : ∀ x, f x ≠ x) :
    ∀ x y : α, P x → P y → ∃ k : Nat, f^[k] x = y := by
  let β := {x : α // P x}
  let g : β → β := fun x => ⟨f x.1, hpres x.1 x.2⟩
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hab)
  have hgfixed : ∀ z : β, g z ≠ z := by
    intro z hz
    exact hfixed z.1 (congrArg Subtype.val hz)
  intro x y hx hy
  let x' : β := ⟨x, hx⟩
  let y' : β := ⟨y, hy⟩
  have hiter : ∀ n (z : β), (g^[n] z).val = f^[n] z.val := by
    intro n
    induction n with
    | zero =>
        intro z
        rfl
    | succ n ih =>
        intro z
        simp [Function.iterate_succ_apply', g, ih]
  obtain ⟨k, hk⟩ := finite_three_injective_fixed_point_free_iterate_transitive_aux__p2m_c087dd6c_81e7_4e4c_ad72_7053d1a189f4_a1
    g hcard hginj hgfixed x' y'
  have hv := congrArg Subtype.val hk
  change (g^[k] x').val = y at hv
  exact ⟨k, (hiter k x').symm.trans hv⟩