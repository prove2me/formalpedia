-- Prove2me | solution 1 for finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:39.260353+00:00
-- url     : https://prove2.me/submissions/e7ab25a4-beb7-4435-b70b-2a86dc4622d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (f : α → α) (P : α → Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : ∀ x, P x → P (f x))
    (hinj : Function.Injective f) (hfixed : ∀ x, f x ≠ x) :
    ∀ x y : α, P x → P y → ∃ k : Nat, f^[k] x = y := by
  let β := {x : α // P x}
  let g : β → β := fun z => ⟨f z.1, hpres z.1 z.2⟩
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact hinj (by simpa [g] using congrArg Subtype.val hab)
  have hg_fixed : ∀ z : β, g z ≠ z := by
    intro z hz
    have hz' : f z.1 = z.1 := by
      simpa [g] using congrArg Subtype.val hz
    exact hfixed z.1 hz'
  have hiter : ∀ k (z : β), (g^[k] z).val = f^[k] z.1 := by
    intro k
    induction k with
    | zero =>
        intro z
        rfl
    | succ k ih =>
        intro z
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change f ((g^[k] z).val) = f (f^[k] z.1)
        exact congrArg f (ih z)
  intro x y hx hy
  obtain ⟨k, hk⟩ :=
    finite_three_cycle_transitive__p2m_a8d65110_f134_4779_9146_a9afc8e73a4c_a1
      g hcard hg_inj hg_fixed ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨k, ?_⟩
  calc
    f^[k] x = (g^[k] ⟨x, hx⟩).val := (hiter k ⟨x, hx⟩).symm
    _ = (⟨y, hy⟩ : β).val := congrArg Subtype.val hk
    _ = y := rfl
