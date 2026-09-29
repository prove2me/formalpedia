-- Prove2me | solution 1 for mme_dwz_table2_all_coarse_Z_outer_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:08:17.47204+00:00
-- url     : https://prove2.me/submissions/18f9aa14-8cea-4c79-aa1e-119a05df9ad3

import Theorems.Thm_mme_dwz_table2_all_coarse_Z_words_card
import Theorems.Thm_mme_dwz_table2_outer_equiv_across_coarse_Z_words

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ)
    (K₀ : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    (hK₀ : ∀ z, Fintype.card {t // K₀ t = z} =
      MME.DWZTable2Counts.alphaZ z * m)
    (I : Type*) [Fintype I]
    (retained : I →
      {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₀ t) ∧
        ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m}) :
    let CoarseWords :=
      {K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 //
        ∀ z, Fintype.card {t // K t = z} =
          MME.DWZTable2Counts.alphaZ z * m}
    let NBZ := Nat.multinomial Finset.univ
      (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m)
    ∃ _indexEquiv : Fin (NBZ * Fintype.card I) ≃ (Σ _ : CoarseWords, I),
      ∃ transported : ∀ K : CoarseWords, I →
          {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
            (∀ t, MME.DWZSquare.shapeZ (w t) = K.1 t) ∧
            ∀ s, Fintype.card {t // w t = s} =
              MME.DWZTable2Counts.component s * m},
        ∀ K, ∃ positionEquiv :
            Fin (MME.DWZTable2Counts.scale * m) ≃
              Fin (MME.DWZTable2Counts.scale * m),
          (∀ t, K.1 (positionEquiv t) = K₀ t) ∧
          ∀ i t, (transported K i).1 (positionEquiv t) =
            (retained i).1 t := by
  classical
  dsimp only
  let CoarseWords :=
    {K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 //
      ∀ z, Fintype.card {t // K t = z} =
        MME.DWZTable2Counts.alphaZ z * m}
  have hKcard :
      Fintype.card CoarseWords =
        Nat.multinomial Finset.univ
          (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) := by
    rw [← Nat.card_eq_fintype_card]
    exact mme_dwz_table2_all_coarse_Z_words_card m
  have hSigma :
      Fintype.card (Σ _ : CoarseWords, I) =
        Nat.multinomial Finset.univ
            (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) *
          Fintype.card I := by
    calc
      Fintype.card (Σ _ : CoarseWords, I) =
          ∑ _ : CoarseWords, Fintype.card I := Fintype.card_sigma
      _ = Fintype.card CoarseWords * Fintype.card I := by simp
      _ = Nat.multinomial Finset.univ
            (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) *
          Fintype.card I := by rw [hKcard]
  let indexEquiv :
      Fin
          (Nat.multinomial Finset.univ
              (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) *
            Fintype.card I) ≃
        (Σ _ : CoarseWords, I) :=
    Fintype.equivOfCardEq (by simpa using hSigma.symm)
  have hTransport : ∀ K : CoarseWords,
      ∃ e : Fin (MME.DWZTable2Counts.scale * m) ≃
          Fin (MME.DWZTable2Counts.scale * m),
        (∀ t, K.1 (e t) = K₀ t) ∧
        ∃ E :
            {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
              (∀ t, MME.DWZSquare.shapeZ (w t) = K₀ t) ∧
              ∀ s, Fintype.card {t // w t = s} =
                MME.DWZTable2Counts.component s * m} ≃
            {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
              (∀ t, MME.DWZSquare.shapeZ (w t) = K.1 t) ∧
              ∀ s, Fintype.card {t // w t = s} =
                MME.DWZTable2Counts.component s * m},
          ∀ w t, (E w).1 (e t) = w.1 t := by
    intro K
    exact mme_dwz_table2_outer_equiv_across_coarse_Z_words
      m K₀ K.1 hK₀ K.2
  choose positionEquiv hposition outerEquiv houter using hTransport
  let transported : ∀ K : CoarseWords, I →
      {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K.1 t) ∧
        ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m} :=
    fun K i ↦ outerEquiv K (retained i)
  refine ⟨indexEquiv, transported, ?_⟩
  intro K
  refine ⟨positionEquiv K, hposition K, ?_⟩
  intro i t
  exact houter K (retained i) t
