-- Prove2me | solution 1 for mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:18:16.03595+00:00
-- url     : https://prove2.me/submissions/0be64da5-5e04-42b9-a1d7-dedf8a75abc0

import Theorems.Thm_mme_dwz_table2_reindexed_marginal_first_hash_retention
import Theorems.Thm_mme_dwz_table2_first_hash_retention_in_canonical_bucket
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_exact_profile_word_card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZGlobalExactProfile

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
  exact Fintype.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl))

private theorem component_z_pushforward (k : Fin 5) :
    (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
        MME.DWZTable2Counts.component s.1) =
      MME.DWZTable2Counts.alphaZ k := by
  rcases mme_dwz_table2_integer_counts_exact with
    ⟨hcomponent, _, _, _, _, _, _, _, hz, _⟩
  apply Nat.cast_injective (R := ℝ)
  calc
    ((∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
        MME.DWZTable2Counts.component s.1 : ℕ) : ℝ) =
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
          (MME.DWZTable2Counts.component s.1 : ℝ) := by norm_cast
    _ = ∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
          (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.alpha s.1 := by
      exact Finset.sum_congr rfl fun s _ ↦ (hcomponent s.1).symm
    _ = (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_marginal MME.DWZSquare.shapeZ
            MME.DWZSquare.alpha k := by
      simp only [mme_modern_marginal, Finset.mul_sum]
    _ = (MME.DWZTable2Counts.alphaZ k : ℝ) := hz k

private theorem exact_profile_has_marginals
    (m : ℕ)
    (w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15)
    (hw : ∀ s, Fintype.card {t // w t = s} =
      MME.DWZTable2Counts.component s * m) :
    (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m) ∧
    (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m) ∧
    ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact composed_fiber_card w MME.DWZSquare.shapeX
      (fun s ↦ MME.DWZTable2Counts.component s * m) hw x
  · intro y
    exact composed_fiber_card w MME.DWZSquare.shapeY
      (fun s ↦ MME.DWZTable2Counts.component s * m) hw y
  · intro z
    calc
      Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
          ∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = z},
            MME.DWZTable2Counts.component s.1 * m :=
        composed_fiber_card w MME.DWZSquare.shapeZ
          (fun s ↦ MME.DWZTable2Counts.component s * m) hw z
      _ = MME.DWZTable2Counts.alphaZ z * m := by
        rw [← Finset.sum_mul, component_z_pushforward]

end MME.DWZGlobalExactProfile

/-- Retain the full exact fifteen-cell Table-2 type family in one literal
canonical affine bucket.  The ambient hash family still has the fixed three
marginals needed to close mixed X/Y words, while the retained target is the
exact joint-profile filter and therefore has cardinality `Nalpha`. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
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
    let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t // a t = s} =
        MME.DWZTable2Counts.component s * m
    ∃ d : ℕ, ∃ A : Finset (Fin (N + 1) → Fin 15),
      (∀ a, a ∈ A ↔ ∃ w ∈ A0,
        (fun t ↦ w (reindex t)) = a) ∧
      A.card = A0.card ∧
      (A.filter ExactProfile).card =
        Nat.multinomial Finset.univ
          (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) ∧
      0 < d ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeX (b t)) =
            (fun t ↦ MME.DWZSquare.shapeX (a t)))).card = d) ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeY (b t)) =
            (fun t ↦ MME.DWZSquare.shapeY (a t)))).card = d) ∧
      (d : ℝ) ≤
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
          (((L + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) ∧
      (4 * d ≤ p →
        ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
          ∃ I : Finset (Fin (N + 1) → Fin 15),
            I ⊆ A.filter ExactProfile ∧
            I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
            (∀ e ∈ I, ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
              (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
            (((A.filter ExactProfile).card : ℝ) * (S.card : ℝ)) /
                (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)) := by
  classical
  dsimp only
  obtain ⟨d, A, hmem, hcard, hd, hx, hy, hrate, _⟩ :=
    mme_dwz_table2_reindexed_marginal_first_hash_retention
      m hm hpodd hp5 S hSrange hSfree
  let L := MME.DWZTable2Counts.scale * m
  let N := L - 1
  let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
    dsimp only [N, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
    { toFun := fun w t ↦ w (reindex t)
      invFun := fun a t ↦ a (reindex.symm t)
      left_inv := fun w ↦ by funext t; simp
      right_inv := fun a ↦ by funext t; simp }
  let Exact0 : Finset (Fin L → Fin 15) := Finset.univ.filter fun w ↦
    ∀ s, Fintype.card {t // w t = s} =
      MME.DWZTable2Counts.component s * m
  let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
    ∀ s, Fintype.card {t // a t = s} =
      MME.DWZTable2Counts.component s * m
  have hfilter : A.filter ExactProfile = Exact0.map W.toEmbedding := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨ha, haExact⟩
      obtain ⟨w, hwA, hwa⟩ := (hmem a).mp ha
      change W w = a at hwa
      subst a
      refine ⟨w, ?_, rfl⟩
      simp only [Exact0, Finset.mem_filter, Finset.mem_univ, true_and]
      intro s
      exact (MME.DWZGlobalExactProfile.reindex_fiber_card
        reindex w s).symm.trans (haExact s)
    · rintro ⟨w, hw, hwa⟩
      change W w = a at hwa
      subst a
      have hwExact : ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m := by
        simpa only [Exact0, Finset.mem_filter, Finset.mem_univ, true_and]
          using hw
      refine ⟨(hmem (W w)).2 ?_, ?_⟩
      · refine ⟨w, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact MME.DWZGlobalExactProfile.exact_profile_has_marginals m w hwExact
      · intro s
        exact (MME.DWZGlobalExactProfile.reindex_fiber_card
          reindex w s).trans (hwExact s)
  have hExact0 : Exact0.card =
      Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) := by
    simpa only [Exact0, L] using mme_dwz_table2_exact_profile_word_card m
  have hTcard : (A.filter ExactProfile).card =
      Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) := by
    rw [hfilter, Finset.card_map, hExact0]
  refine ⟨d, A, hmem, hcard, hTcard, hd, hx, hy, hrate, ?_⟩
  intro hmod
  exact mme_dwz_table2_first_hash_retention_in_canonical_bucket
    hpodd hp5 S hSrange hSfree A (A.filter ExactProfile)
      (fun _ h ↦ (Finset.mem_filter.mp h).1) d hmod
      (fun a ha ↦ (hx a (Finset.mem_filter.mp ha).1).le)
      (fun a ha ↦ (hy a (Finset.mem_filter.mp ha).1).le)
