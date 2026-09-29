-- Prove2me | solution 1 for mme_dwz_table2_fixed_K_reindexed_target_equiv_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:31:46.344935+00:00
-- url     : https://prove2.me/submissions/36f3247a-4c44-4699-9db9-1efdbebfe5fe

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZFixedKTargetOuter

private def wordReindexEquiv {α β σ : Type*} (e : β ≃ α) :
    (α → σ) ≃ (β → σ) where
  toFun w t := w (e t)
  invFun w t := w (e.symm t)
  left_inv w := by funext t; simp
  right_inv w := by funext t; simp

private def composedFiberEquiv
    {ι σ κ : Type*} (w : ι → σ) (f : σ → κ) (k : κ) :
    {t : ι // f (w t) = k} ≃
      Σ s : {s : σ // f s = k}, {t : ι // w t = s.1} where
  toFun t := ⟨⟨w t.1, t.2⟩, ⟨t.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
  left_inv t := by rfl
  right_inv x := by
    rcases x with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    cases ht
    rfl

private theorem composed_fiber_card
    {ι σ κ : Type*} [Fintype ι] [Fintype σ] [Fintype κ]
    [DecidableEq σ] [DecidableEq κ]
    (w : ι → σ) (f : σ → κ) (counts : σ → ℕ)
    (hcounts : ∀ s, Fintype.card {t : ι // w t = s} = counts s)
    (k : κ) :
    Fintype.card {t : ι // f (w t) = k} =
      ∑ s : {s : σ // f s = k}, counts s.1 := by
  rw [Fintype.card_congr (composedFiberEquiv w f k), Fintype.card_sigma]
  exact Finset.sum_congr rfl fun s _ ↦ hcounts s.1

private theorem reindex_fiber_card
    {α β σ : Type*} [Fintype α] [Fintype β] [DecidableEq σ]
    (e : β ≃ α) (w : α → σ) (s : σ) :
    Fintype.card {t : β // w (e t) = s} =
      Fintype.card {t : α // w t = s} := by
  exact Fintype.card_congr
    (e.subtypeEquiv (fun _ ↦ Iff.rfl))

private theorem component_z_pushforward (k : Fin 5) :
    (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
        MME.DWZTable2Counts.component s.1) =
      MME.DWZTable2Counts.alphaZ k := by
  fin_cases k <;> decide

end MME.DWZFixedKTargetOuter

/-- The fixed-`K` target finset used by the first hash is exactly the literal
fixed-coarse-word `Outer` type used by Claim 6.8, after undoing the positive-
length coordinate reindexing.  In particular their finite cardinalities are
equal, so the first-hash lower bound has the source cardinal `Nα / NBZ`. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5) :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
      { toFun := fun w t ↦ w (reindex t)
        invFun := fun w t ↦ w (reindex.symm t)
        left_inv := fun w ↦ by funext t; simp
        right_inv := fun w ↦ by funext t; simp }
    let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
    let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    let T := A.filter FixedK
    let Outer :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    ∃ e : {a : Fin (N + 1) → Fin 15 // a ∈ T} ≃ Outer,
      (∀ a, (e a).1 = fun t ↦ a.1 (reindex.symm t)) ∧
      T.card = Nat.card Outer := by
  classical
  dsimp only
  let L := MME.DWZTable2Counts.scale * m
  let N := L - 1
  have hL : N + 1 = L := by
    dsimp only [N, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm)))
  let reindex : Fin (N + 1) ≃ Fin L := finCongr hL
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let P : (Fin L → Fin 15) → Prop := fun w ↦
    (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
    (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
    ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m
  let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
  let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
    MME.DWZFixedKTargetOuter.wordReindexEquiv reindex
  let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
  let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
    (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
    ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
      MME.DWZTable2Counts.component s * m
  let T := A.filter FixedK
  let Outer :=
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m}
  have outer_mem_A0 (w : Outer) : w.1 ∈ A0 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro x
      exact MME.DWZFixedKTargetOuter.composed_fiber_card
        w.1 MME.DWZSquare.shapeX
          (fun s ↦ MME.DWZTable2Counts.component s * m) w.2.2 x
    · intro y
      exact MME.DWZFixedKTargetOuter.composed_fiber_card
        w.1 MME.DWZSquare.shapeY
          (fun s ↦ MME.DWZTable2Counts.component s * m) w.2.2 y
    · intro z
      calc
        Fintype.card {t : Fin L // MME.DWZSquare.shapeZ (w.1 t) = z} =
            ∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = z},
              MME.DWZTable2Counts.component s.1 * m :=
          MME.DWZFixedKTargetOuter.composed_fiber_card
            w.1 MME.DWZSquare.shapeZ
              (fun s ↦ MME.DWZTable2Counts.component s * m) w.2.2 z
        _ = MME.DWZTable2Counts.alphaZ z * m := by
          rw [← Finset.sum_mul,
            MME.DWZFixedKTargetOuter.component_z_pushforward]
  have outer_mem_T (w : Outer) : W w.1 ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_map.mpr ⟨w.1, outer_mem_A0 w, rfl⟩, ?_, ?_⟩
    · intro t
      exact w.2.1 (reindex t)
    · intro s
      exact (MME.DWZFixedKTargetOuter.reindex_fiber_card
        reindex w.1 s).trans (w.2.2 s)
  let toOuter : {a : Fin (N + 1) → Fin 15 // a ∈ T} → Outer := fun a ↦
    ⟨W.symm a.1, by
      have haFixed := (Finset.mem_filter.mp a.2).2
      constructor
      · intro t
        have h := haFixed.1 (reindex.symm t)
        simpa only [W, MME.DWZFixedKTargetOuter.wordReindexEquiv,
          Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply] using h
      · intro s
        have h := haFixed.2 s
        rw [← h]
        exact (MME.DWZFixedKTargetOuter.reindex_fiber_card
          reindex (W.symm a.1) s).symm⟩
  let toTarget : Outer → {a : Fin (N + 1) → Fin 15 // a ∈ T} := fun w ↦
    ⟨W w.1, outer_mem_T w⟩
  let e : {a : Fin (N + 1) → Fin 15 // a ∈ T} ≃ Outer :=
    { toFun := toOuter
      invFun := toTarget
      left_inv := by
        intro a
        apply Subtype.ext
        exact W.apply_symm_apply a.1
      right_inv := by
        intro w
        apply Subtype.ext
        exact W.symm_apply_apply w.1 }
  refine ⟨e, ?_, ?_⟩
  · intro a
    rfl
  · rw [← Fintype.card_coe]
    exact (Fintype.card_congr e).trans Nat.card_eq_fintype_card.symm
