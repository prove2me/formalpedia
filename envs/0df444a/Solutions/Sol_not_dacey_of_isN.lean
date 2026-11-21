-- Prove2me | solution 1 for not_dacey_of_isN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:11:25.268172+00:00
-- url     : https://prove2.me/submissions/349fcdc5-2c1a-41d7-a02a-b29c12aac6b8

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
import Theorems.Thm_orthComp_orthComp_orthComp
import Theorems.Thm_chardacey
attribute [local simp] perp_iff

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution [Finite P] {a b c d : P} (hN : IsN a b c d) :
    ¬ IsDacey P := by
  obtain ⟨hac, hbc, hbd, hab, had, hcd⟩ := hN
  -- X = {x | x < c ∧ ¬ x ≤ d}
  let X : Set P := {x | x < c ∧ ¬ x ≤ d}
  -- Claim 1: d ∈ X⊥
  have hdXp : d ∈ orthComp X := fun x hx =>
    ⟨hx.2, fun hdx => hcd.2 (hdx.trans_lt hx.1).le⟩
  -- Let B be a basis of X⊥ with d ∈ B (exists by taking a maximal pairwise orthogonal subset containing d)
  obtain ⟨B, hBbase, hdB⟩ : ∃ B : Set P, IsOrthoBase B (orthComp X) ∧ d ∈ B := by
    haveI : Fintype P := Fintype.ofFinite P
    haveI : DecidableEq P := Classical.decEq P
    haveI : DecidableRel (α := P) (· ⊥ ·) := fun _ _ => Classical.dec _
    haveI : DecidablePred (fun S : Finset P =>
        (∀ x ∈ S, x ∈ orthComp X) ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ⊥ y) ∧ d ∈ S) :=
      fun _ => Classical.dec _
    let coll : Finset (Finset P) := Finset.univ.powerset.filter fun S =>
      (∀ x ∈ S, x ∈ orthComp X) ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ⊥ y) ∧ d ∈ S
    have hne : coll.Nonempty := ⟨{d}, by
      simp only [coll, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      exact ⟨fun x hx => (Finset.mem_singleton.mp hx) ▸ hdXp,
             fun x hx y hy hne => absurd
               ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm) hne,
             Finset.mem_singleton_self d⟩⟩
    obtain ⟨B₀, hB₀mem, hB₀max⟩ := coll.exists_maximal hne
    simp only [coll, Finset.mem_filter, Finset.mem_powerset] at hB₀mem
    obtain ⟨-, hB₀sub, hB₀po, hdB₀⟩ := hB₀mem
    refine ⟨(B₀ : Set P), ⟨fun x hx => hB₀sub x (Finset.mem_coe.mp hx),
      fun x hx y hy hne => hB₀po x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne,
      fun x hxXp hxB => by
        by_contra hxB₀
        have hinsert : insert x B₀ ∈ coll := by
          simp only [coll, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
          refine ⟨fun e he => ?_, fun u hu v hv huv => ?_, Finset.mem_insert_of_mem hdB₀⟩
          · rcases Finset.mem_insert.mp he with rfl | he
            · exact hxXp
            · exact hB₀sub e he
          · rcases Finset.mem_insert.mp hu with rfl | hu'
            · rcases Finset.mem_insert.mp hv with rfl | hv'
              · exact absurd rfl huv
              · exact hxB v (Finset.mem_coe.mpr hv')
            · rcases Finset.mem_insert.mp hv with rfl | hv'
              · exact Orthoset.perp_symm (hxB u (Finset.mem_coe.mpr hu'))
              · exact hB₀po u hu' v hv' huv
        exact hxB₀ (Finset.mem_coe.mpr
          (Finset.insert_subset_iff.mp (hB₀max hinsert (Finset.subset_insert x B₀))).1)⟩,
      Finset.mem_coe.mpr hdB₀⟩
  -- Claim 2: c ∈ B⊥
  have hcBp : c ∈ orthComp B := by
    intro y hyB
    have hyXp : y ∈ orthComp X := hBbase.1 hyB
    by_contra hcy
    simp only [perp_iff, not_and_or, not_not] at hcy
    -- y ≠ d (c ⊥ d but ¬ c ⊥ y), so y ⊥ d by pairwise orthogonality of B
    have hyd : y ⊥ d := by
      apply hBbase.2.1 y hyB d hdB
      intro heq; subst heq
      rcases hcy with h | h
      · exact hcd.2 h
      · exact hcd.1 h
    rcases hcy with hcy | hyc
    · -- y ≤ c: y < c or y = c
      rcases hcy.lt_or_eq with hyc | hyc
      · -- y < c and ¬ y ≤ d: y ∈ X, but y ∈ X⊥ gives y ⊥ y — irrefl
        exact Orthoset.perp_irrefl y (hyXp y ⟨hyc, hyd.1⟩)
      · -- y = c: c ∈ X⊥, a ∈ X gives a ⊥ c, but a < c contradicts ¬ a ≤ c
        exact (hyc ▸ hyXp) a ⟨hac, had.1⟩ |>.1 hac.le
    · -- c ≤ y: a < c ≤ y contradicts a ⊥ y (a ∈ X, y ∈ X⊥)
      exact (hyXp a ⟨hac, had.1⟩).1 (hac.le.trans hyc)
  -- Claim 3: b ∈ X⊥
  have hbXp : b ∈ orthComp X := by
    intro x hx
    refine ⟨fun hxb => hx.2 (hxb.trans hbd.le), fun hbx => ?_⟩
    rcases hbx.lt_or_eq with hbxlt | hbxeq
    · exact hbc.2 hbxlt hx.1
    · exact hx.2 (hbxeq ▸ hbd.le)
  -- Now show ¬ IsDacey P by applying IsDacey to orthComp X
  intro hDacey
  have hXpClosed : IsOrthoclosed (orthComp X) := orthComp_orthComp_orthComp X
  have hDSub : IsDaceySubset (orthComp X) := hDacey (orthComp X) hXpClosed
  rw [chardacey hXpClosed] at hDSub
  -- c ∈ orthComp B (Claim 2), so c ∈ orthComp (orthComp X)
  have hcXpp : c ∈ orthComp (orthComp X) := hDSub B hBbase hcBp
  -- but b ∈ orthComp X and ¬ c ⊥ b (since b < c)
  exact (hcXpp b hbXp).1 hbc.le
