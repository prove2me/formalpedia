-- Prove2me | solution 1 for finite_three_injective_fixed_point_free_iterate_transitive__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:32:17.949657+00:00
-- url     : https://prove2.me/submissions/034a4793-6fb4-42f7-b669-8ad6620efa42

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (f : α → α) (P : α → Prop) [DecidablePred P]
    (hcard : Fintype.card {x : α // P x} = 3)
    (hpres : ∀ x, P x → P (f x))
    (hinj : Function.Injective f) (hfixed : ∀ x, ¬ f x = x) :
    ∀ x y : α, P x → P y → ∃ k : Nat, f^[k] x = y := by
  classical
  intro x y hx hy
  let β := {z : α // P z}
  let g : β → β := fun z => ⟨f z.1, hpres z.1 z.2⟩
  have hginj : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  have hgnofix : ∀ z : β, ¬ g z = z := by
    intro z hz
    exact hfixed z.1 (congrArg Subtype.val hz)
  let a : β := ⟨x, hx⟩
  let b : β := g a
  let s : Finset β := {a, b}
  have hab : a ≠ b := by
    intro h
    apply hgnofix a
    exact h.symm
  have hs : s.card = 2 := by
    dsimp [s]
    exact Finset.card_pair_eq_two_iff.mpr hab
  have hlt : s.card < Fintype.card β := by
    rw [hs]
    change 2 < Fintype.card {z : α // P z}
    rw [hcard]
    decide
  obtain ⟨d, _, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hda : d ≠ a := by
    intro h
    apply hdnot
    simp [s, h]
  have hdb : d ≠ b := by
    intro h
    apply hdnot
    simp [s, h]
  have habd : ({a, b, d} : Finset β).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hab, hda.symm, hdb.symm⟩
  have hcover : ({a, b, d} : Finset β) = Finset.univ := by
    apply Finset.eq_univ_of_card
    change ({a, b, d} : Finset β).card = Fintype.card {z : α // P z}
    rw [hcard]
    exact habd
  let c : β := g b
  have hca : c ≠ a := by
    intro h
    have hdbA : g d ≠ a := by
      intro hga
      have heq : g d = g b := hga.trans h.symm
      have hdEq : d = b := hginj heq
      apply hdnot
      simp [s, hdEq]
    have hdbB : g d ≠ b := by
      intro hgb
      have heq : g d = g a := hgb.trans rfl
      have hdEq : d = a := hginj heq
      apply hdnot
      simp [s, hdEq]
    have hgd : g d = d := by
      have hmem : g d ∈ ({a, b, d} : Finset β) := by
        rw [hcover]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hga | hgb | hgd
      · exact (hdbA hga).elim
      · exact (hdbB hgb).elim
      · exact hgd
    exact hgnofix d hgd
  have hcb : c ≠ b := by
    intro h
    exact hgnofix b h
  have htriple : ({a, b, c} : Finset β).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hab, hca.symm, hcb.symm⟩
  have hcoverABC : ({a, b, c} : Finset β) = Finset.univ := by
    apply Finset.eq_univ_of_card
    change ({a, b, c} : Finset β).card = Fintype.card {z : α // P z}
    rw [hcard]
    exact htriple
  have hyS : (⟨y, hy⟩ : β) ∈ ({a, b, c} : Finset β) := by
    rw [hcoverABC]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyS
  rcases hyS with hya | hyb | hyc
  · refine ⟨0, ?_⟩
    simpa [a] using (congrArg Subtype.val hya).symm
  · refine ⟨1, ?_⟩
    have hv := (congrArg Subtype.val hyb).symm
    simpa [Function.iterate_succ_apply, a, b, g] using hv
  · refine ⟨2, ?_⟩
    have hv := (congrArg Subtype.val hyc).symm
    simpa [Function.iterate_succ_apply, a, b, c, g] using hv
