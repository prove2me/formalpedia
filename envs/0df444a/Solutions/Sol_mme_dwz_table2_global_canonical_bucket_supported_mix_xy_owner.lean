-- Prove2me | solution 1 for mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T14:33:40.096934+00:00
-- url     : https://prove2.me/submissions/bb6adcba-e139-4147-b4f8-ce28d806c7e9

import Definitions.Def_mme_dwz_table2_affine_hash_bucket

open MME

set_option autoImplicit false
set_option warningAsError true

private theorem table2_shape_exists_of_sum
    (x y z : Fin 5) (h : x.val + y.val + z.val = 4) :
    ∃ s : Fin 15,
      MME.DWZSquare.shapeX s = x ∧
      MME.DWZSquare.shapeY s = y ∧
      MME.DWZSquare.shapeZ s = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num at h <;> decide

theorem solution
    {p N k : ℕ} [Fact p.Prime]
    (S : Finset ℕ)
    (A I : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (alphaX alphaY alphaZ : Fin 5 → ℕ)
    (hA : ∀ e, e ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (e t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (e t) = y} = alphaY y) ∧
      (∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (e t) = z} = alphaZ z))
    (outer : Fin k → Fin (N + 1) → Fin 15)
    (houter_injective : Function.Injective outer)
    (houter : ∀ j, outer j ∈ I)
    (hbucket : I ⊆ MME.dwzTable2AffineHashBucket S A q)
    (hisolated : ∀ e ∈ I,
      ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
        (fun t ↦ MME.DWZSquare.shapeX (e t)) =
            (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
          (fun t ↦ MME.DWZSquare.shapeY (e t)) =
            (fun t ↦ MME.DWZSquare.shapeY (e' t)) →
        e = e')
    (js : Fin 3 → Fin k)
    (hsupported : ∀ t : Fin (N + 1),
      (MME.DWZSquare.shapeX (outer (js 0) t)).val +
        (MME.DWZSquare.shapeY (outer (js 1) t)).val +
        (MME.DWZSquare.shapeZ (outer (js 2) t)).val = 4) :
    js 0 = js 1 := by
  classical
  let witness : ∀ t : Fin (N + 1), ∃ s : Fin 15,
      MME.DWZSquare.shapeX s = MME.DWZSquare.shapeX (outer (js 0) t) ∧
      MME.DWZSquare.shapeY s = MME.DWZSquare.shapeY (outer (js 1) t) ∧
      MME.DWZSquare.shapeZ s = MME.DWZSquare.shapeZ (outer (js 2) t) :=
    fun t ↦ table2_shape_exists_of_sum _ _ _ (hsupported t)
  let mixed : Fin (N + 1) → Fin 15 := fun t ↦ Classical.choose (witness t)
  have hmixedX : (fun t ↦ MME.DWZSquare.shapeX (mixed t)) =
      (fun t ↦ MME.DWZSquare.shapeX (outer (js 0) t)) := by
    funext t
    exact (Classical.choose_spec (witness t)).1
  have hmixedY : (fun t ↦ MME.DWZSquare.shapeY (mixed t)) =
      (fun t ↦ MME.DWZSquare.shapeY (outer (js 1) t)) := by
    funext t
    exact (Classical.choose_spec (witness t)).2.1
  have hmixedZ : (fun t ↦ MME.DWZSquare.shapeZ (mixed t)) =
      (fun t ↦ MME.DWZSquare.shapeZ (outer (js 2) t)) := by
    funext t
    exact (Classical.choose_spec (witness t)).2.2
  have houterA : ∀ j, outer j ∈ A := by
    intro j
    exact (Finset.mem_filter.mp (hbucket (houter j))).1
  have hmixedA : mixed ∈ A := by
    rw [hA]
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa only [congrFun hmixedX] using
        ((hA (outer (js 0))).mp (houterA (js 0))).1 x
    · intro y
      simpa only [congrFun hmixedY] using
        ((hA (outer (js 1))).mp (houterA (js 1))).2.1 y
    · intro z
      simpa only [congrFun hmixedZ] using
        ((hA (outer (js 2))).mp (houterA (js 2))).2.2 z
  have hmixedBucket : mixed ∈ MME.dwzTable2AffineHashBucket S A q := by
    simp only [MME.dwzTable2AffineHashBucket, Finset.mem_filter, hmixedA,
      true_and]
    have h0 := Finset.mem_filter.mp (hbucket (houter (js 0)))
    have h1 := Finset.mem_filter.mp (hbucket (houter (js 1)))
    have h2 := Finset.mem_filter.mp (hbucket (houter (js 2)))
    have hcastX : MME.dwzTable2CastX (p := p) mixed =
        MME.dwzTable2CastX (p := p) (outer (js 0)) := by
      funext t
      simp only [MME.dwzTable2CastX, congrFun hmixedX]
    have hcastY : MME.dwzTable2CastY (p := p) mixed =
        MME.dwzTable2CastY (p := p) (outer (js 1)) := by
      funext t
      simp only [MME.dwzTable2CastY, congrFun hmixedY]
    have hcastZ : MME.dwzTable2CastZ (p := p) mixed =
        MME.dwzTable2CastZ (p := p) (outer (js 2)) := by
      funext t
      simp only [MME.dwzTable2CastZ, congrFun hmixedZ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcastX]
      exact h0.2.1
    · rw [hcastY]
      exact h1.2.2.1
    · rw [hcastZ]
      exact h2.2.2.2
  have h0mixed : outer (js 0) = mixed :=
    hisolated (outer (js 0)) (houter (js 0)) mixed hmixedBucket
      (Or.inl hmixedX.symm)
  have h1mixed : outer (js 1) = mixed :=
    hisolated (outer (js 1)) (houter (js 1)) mixed hmixedBucket
      (Or.inr hmixedY.symm)
  exact houter_injective (h0mixed.trans h1mixed.symm)
