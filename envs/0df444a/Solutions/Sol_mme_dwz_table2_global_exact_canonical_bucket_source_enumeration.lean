-- Prove2me | solution 1 for mme_dwz_table2_global_exact_canonical_bucket_source_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:58:52.142527+00:00
-- url     : https://prove2.me/submissions/afb8b416-0fa2-403f-ae89-d108fda827d2

import Theorems.Thm_mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner

open MME

set_option autoImplicit false
set_option warningAsError true

/-- Enumerate every retained exact-profile word in source coordinate order.
No owner is lost: reindexing the result gives the literal member of `I`.
The global first-hash isolation consequently identifies the X and Y owners
of every coordinatewise supported mixed triple. -/
theorem solution
    {p N L k : ℕ} [Fact p.Prime]
    (reindex : Fin (N + 1) ≃ Fin L)
    (S : Finset ℕ)
    (A I : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (counts : Fin 15 → ℕ)
    (alphaX alphaY alphaZ : Fin 5 → ℕ)
    (hcard : I.card = k)
    (hA : ∀ e, e ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (e t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (e t) = y} = alphaY y) ∧
      (∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (e t) = z} = alphaZ z))
    (hexact : I ⊆ A.filter fun e ↦
      ∀ s, Fintype.card {t : Fin (N + 1) // e t = s} = counts s)
    (hbucket : I ⊆ MME.dwzTable2AffineHashBucket S A q)
    (hisolated : ∀ e ∈ I,
      ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
        (fun t ↦ MME.DWZSquare.shapeX (e t)) =
            (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
          (fun t ↦ MME.DWZSquare.shapeY (e t)) =
            (fun t ↦ MME.DWZSquare.shapeY (e' t)) →
        e = e') :
    ∃ outer : Fin k → Fin L → Fin 15,
      Function.Injective outer ∧
      (∀ j, (fun t ↦ outer j (reindex t)) ∈ I) ∧
      (∀ j s, Fintype.card {t : Fin L // outer j t = s} = counts s) ∧
      ∀ js : Fin 3 → Fin k,
        (∀ t : Fin L,
          (MME.DWZSquare.shapeX (outer (js 0) t)).val +
            (MME.DWZSquare.shapeY (outer (js 1) t)).val +
            (MME.DWZSquare.shapeZ (outer (js 2) t)).val = 4) →
        js 0 = js 1 := by
  classical
  subst k
  let enum : Fin I.card ≃ ↥I := I.equivFin.symm
  let retained : Fin I.card → Fin (N + 1) → Fin 15 :=
    fun j ↦ (enum j).1
  let outer : Fin I.card → Fin L → Fin 15 :=
    fun j t ↦ retained j (reindex.symm t)
  have hretainedInjective : Function.Injective retained := by
    intro j j' h
    exact enum.injective (Subtype.ext h)
  have houterInjective : Function.Injective outer := by
    intro j j' h
    apply hretainedInjective
    funext t
    have ht := congrFun h (reindex t)
    simpa only [outer, retained, Equiv.symm_apply_apply] using ht
  have hretainedI : ∀ j, retained j ∈ I := fun j ↦ (enum j).2
  have hreindex : ∀ j, (fun t ↦ outer j (reindex t)) = retained j := by
    intro j
    funext t
    simp only [outer, Equiv.symm_apply_apply]
  refine ⟨outer, houterInjective, ?_, ?_, ?_⟩
  · intro j
    rw [hreindex j]
    exact hretainedI j
  · intro j s
    have hR := (Finset.mem_filter.mp (hexact (hretainedI j))).2 s
    calc
      Fintype.card {t : Fin L // outer j t = s} =
          Fintype.card {t : Fin (N + 1) // retained j t = s} := by
        exact Fintype.card_congr
          (reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl))
      _ = counts s := hR
  · intro js hsupported
    apply mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
      S A I q alphaX alphaY alphaZ hA retained hretainedInjective
        hretainedI hbucket hisolated js
    intro t
    have ht := hsupported (reindex t)
    simpa only [outer, Equiv.symm_apply_apply] using ht
