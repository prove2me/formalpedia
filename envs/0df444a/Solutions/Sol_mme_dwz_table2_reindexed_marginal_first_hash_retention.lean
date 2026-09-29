-- Prove2me | solution 1 for mme_dwz_table2_reindexed_marginal_first_hash_retention
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:19:27.271499+00:00
-- url     : https://prove2.me/submissions/5f6a8e2d-626e-4724-8fac-20e08f7a1e7e

import Theorems.Thm_mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
import Theorems.Thm_mme_dwz_table2_raw_marginal_family_uniform_xy_degree

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

open MME

private def wordReindexEquiv {α β σ : Type*} (e : β ≃ α) :
    (α → σ) ≃ (β → σ) where
  toFun w t := w (e t)
  invFun w t := w (e.symm t)
  left_inv w := by
    funext t
    simp
  right_inv w := by
    funext t
    simp

private theorem reindex_star_card
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [DecidableEq σ] [DecidableEq κ]
    (e : β ≃ α) (coord : σ → κ)
    (A : Finset (α → σ)) (a : α → σ) :
    (((A.map (wordReindexEquiv e).toEmbedding).filter (fun b ↦
      (fun t ↦ coord (b t)) =
        (fun t ↦ coord ((wordReindexEquiv e a) t)))).card) =
      (A.filter (fun b ↦
        (fun t ↦ coord (b t)) = (fun t ↦ coord (a t)))).card := by
  classical
  let W : (α → σ) ≃ (β → σ) := wordReindexEquiv e
  have hfin :
      (A.map W.toEmbedding).filter (fun b ↦
          (fun t ↦ coord (b t)) =
            (fun t ↦ coord ((W a) t))) =
        (A.filter (fun b ↦
          (fun t ↦ coord (b t)) =
            (fun t ↦ coord (a t)))).map W.toEmbedding := by
    ext v
    constructor
    · intro hv
      have hv' := Finset.mem_filter.mp hv
      obtain ⟨w, hwA, hwv⟩ := Finset.mem_map.mp hv'.1
      subst v
      apply Finset.mem_map.mpr
      refine ⟨w, Finset.mem_filter.mpr ⟨hwA, ?_⟩, rfl⟩
      funext u
      have hu := congrFun hv'.2 (e.symm u)
      change coord (w (e (e.symm u))) = coord (a (e (e.symm u))) at hu
      simpa only [Equiv.apply_symm_apply] using hu
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_map.mp hv
      subst v
      have hw' := Finset.mem_filter.mp hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_map.mpr ⟨w, hw'.1, rfl⟩, ?_⟩
      funext t
      exact congrFun hw'.2 (e t)
  rw [hfin, Finset.card_map]

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
    ∃ d : ℕ, ∃ A : Finset (Fin (N + 1) → Fin 15),
      (∀ a, a ∈ A ↔ ∃ w ∈ A0,
        (fun t ↦ w (reindex t)) = a) ∧
      A.card = A0.card ∧
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
        ∃ E : ((Fin (N + 2) → ZMod p) × ZMod p) →
            Finset (Fin (N + 1) → Fin 15),
          (∀ q, E q ⊆ A) ∧
          ∃ q, ∃ I : Finset (Fin (N + 1) → Fin 15),
            I ⊆ A ∧ I ⊆ E q ∧
            (∀ e ∈ I, ∀ e' ∈ E q,
              (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
            ((A.card : ℝ) * (S.card : ℝ)) /
                (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)) := by
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
  have hraw := mme_dwz_table2_raw_marginal_family_uniform_xy_degree m
  dsimp only at hraw
  obtain ⟨d, hd, hx0, hy0, hrate⟩ := hraw
  let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
    wordReindexEquiv reindex
  let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
  have hmem (a : Fin (N + 1) → Fin 15) :
      a ∈ A ↔ ∃ w ∈ A0, (fun t ↦ w (reindex t)) = a := by
    simp only [A, Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, hwa⟩
      exact ⟨w, hw, hwa⟩
  have hcard : A.card = A0.card := Finset.card_map _
  have hxA : ∀ a ∈ A,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeX (b t)) =
          (fun t ↦ MME.DWZSquare.shapeX (a t)))).card = d := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.mp ha
    exact (reindex_star_card reindex MME.DWZSquare.shapeX A0 a0).trans
      (hx0 a0 ha0)
  have hyA : ∀ a ∈ A,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeY (b t)) =
          (fun t ↦ MME.DWZSquare.shapeY (a t)))).card = d := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.mp ha
    exact (reindex_star_card reindex MME.DWZSquare.shapeY A0 a0).trans
      (hy0 a0 ha0)
  refine ⟨d, A, hmem, hcard, hd, hxA, hyA, hrate, ?_⟩
  intro hmod
  have hret := mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
    hpodd hp5 S hSrange hSfree A A (fun _ h ↦ h) d hmod
      (fun a ha ↦ (hxA a ha).le) (fun a ha ↦ (hyA a ha).le)
  simpa only using hret
