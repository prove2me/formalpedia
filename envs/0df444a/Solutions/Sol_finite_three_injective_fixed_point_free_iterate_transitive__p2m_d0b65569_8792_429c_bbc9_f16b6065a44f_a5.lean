-- Prove2me | solution 1 for finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T14:28:07.830671+00:00
-- url     : https://prove2.me/submissions/6d356799-ba69-44f8-8276-33f2b84391b8

import Mathlib

set_option autoImplicit false

/-- A fixed-point-free permutation preserving a 3-element predicate acts transitively on it. -/
theorem solution {α : Type} [Fintype α] (f : α → α) (P : α → Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : ∀ x, P x → P (f x))
    (hinj : Function.Injective f) (hfixed : ∀ x, f x ≠ x) :
    ∀ x y : α, P x → P y → ∃ k : Nat, f^[k] x = y := by
  classical
  let S := {x : α // P x}
  let g : S → S := fun x => ⟨f x.1, hpres x.1 x.2⟩
  have hcardS : Fintype.card S = 3 := hcard
  have hg_val : ∀ (x : S) (k : Nat), (g^[k] x).1 = f^[k] x.1 := by
    intro x k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change f (g^[n] x).1 = f^[n + 1] x.1
      rw [ih, Function.iterate_succ_apply']
  have hg_inj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  have hg_fixed : ∀ x : S, g x ≠ x := by
    intro x h
    exact hfixed x.1 (congrArg Subtype.val h)
  have key : ∀ x y : S, ∃ k : Nat, g^[k] x = y := by
    intro x y
    have h2 : g^[2] x ≠ x := by
      intro hxx
      have hgy : g (g x) = x := by simpa using hxx
      have hxne : x ≠ g x := (hg_fixed x).symm
      let C : Finset S := Finset.univ \ {x, g x}
      have hpair : ({x, g x} : Finset S).card = 2 := Finset.card_pair hxne
      have hCcard : C.card = 1 := by
        dsimp only [C]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcardS, hpair]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hCcard
      have hwC : w ∈ C := by rw [hw]; exact Finset.mem_singleton_self w
      have hw_not : w ∉ ({x, g x} : Finset S) := by
        have h := hwC
        simp only [C, Finset.mem_sdiff] at h
        exact h.2
      have hwx : w ≠ x := by
        intro h
        exact hw_not (by rw [h]; exact Finset.mem_insert_self _ _)
      have hwgx : w ≠ g x := by
        intro h
        exact hw_not (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hgw_not : g w ∉ ({x, g x} : Finset S) := by
        intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · have : w = g x := hg_inj (by rw [h, hgy])
          exact hwgx this
        · exact hwx (hg_inj h)
      have hgwC : g w ∈ C := by
        simp only [C, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hgw_not⟩
      have hgw : g w = w := by
        rw [hw] at hgwC
        simpa using hgwC
      exact hg_fixed w hgw
    have hx1 : x ≠ g x := (hg_fixed x).symm
    have hx2 : x ≠ g^[2] x := fun h => h2 h.symm
    have h12 : g x ≠ g^[2] x := by
      intro h
      have hgx : g (g x) = g x := by
        have h' : g^[2] x = g x := h.symm
        simpa using h'
      exact hx1 (hg_inj hgx).symm
    have hx_notin : x ∉ ({g x, g^[2] x} : Finset S) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hx1 h
      · exact hx2 h
    have hgx_notin : g x ∉ ({g^[2] x} : Finset S) := by
      simp only [Finset.mem_singleton]
      exact h12
    have htriple : ({x, g x, g^[2] x} : Finset S).card = 3 := by
      rw [Finset.card_insert_of_notMem hx_notin, Finset.card_insert_of_notMem hgx_notin,
        Finset.card_singleton]
    have huniv : ({x, g x, g^[2] x} : Finset S) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [htriple, hcardS])
    have hy : y ∈ ({x, g x, g^[2] x} : Finset S) := by
      rw [huniv]
      exact Finset.mem_univ y
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
  intro x y hx hy
  obtain ⟨k, hk⟩ := key ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have hv := hg_val ⟨x, hx⟩ k
  rw [hk] at hv
  exact hv.symm
