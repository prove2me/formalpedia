-- Prove2me | solution 1 for infinite_ramsey_seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:04.742175+00:00
-- url     : https://prove2.me/submissions/fa516449-06cf-4c4f-8d51-69e042c17076

module
public import Mathlib.Data.Finset.Card
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Theorems.Thm_infinite_ramsey
public import Theorems.Thm_Set_Infinite_exists_strictMono


set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
variable {κ : Type*}
theorem _root_.solution [Finite κ] (r : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = r → c t = col := by
  obtain ⟨N, _, hNinf, col, hcol⟩ := infinite_ramsey r c (M := Set.univ) Set.infinite_univ
  obtain ⟨e, he, hmem⟩ := hNinf.exists_strictMono
  exact ⟨e, he, col, fun t htsub htcard =>
    hcol t (htsub.trans (Set.range_subset_iff.mpr hmem)) htcard⟩
