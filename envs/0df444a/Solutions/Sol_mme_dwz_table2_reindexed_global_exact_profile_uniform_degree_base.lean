-- Prove2me | solution 1 for mme_dwz_table2_reindexed_global_exact_profile_uniform_degree_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T07:19:12.959468+00:00
-- url     : https://prove2.me/submissions/297f4b4b-a4d0-4b0a-a1ee-f453aedd63e6

import Theorems.Thm_mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m) :
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
                    MME.DWZSquare.alpha))) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h :=
    mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention
      m hm (p := 5) (by decide) (by decide) ∅ (by simp) (by simp)
  simpa only using h.imp fun d hd ↦ hd.imp fun A hA ↦
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1,
      hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1⟩
