-- Prove2me | solution 1 for mme_dwz_table2_typical_denominator_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T12:55:32.671278+00:00
-- url     : https://prove2.me/submissions/8ee97317-951c-48bf-b374-b58af97f37d3

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_gamma_pushforward

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution (m : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let BtypicalK :=
        {small : Fin (MME.DWZTable2Counts.scale * m) → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ p, Fintype.card {t // small t = p} =
            MME.DWZTable2Counts.gamma p * m}
      (∀ k, Fintype.card {t // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nat.card BtypicalK =
          ∏ k, Nat.multinomial Finset.univ
            (fun p : {p : Fin 3 × Fin 3 //
                MME.DWZTable2Counts.coarseOf p = k} =>
              MME.DWZTable2Counts.gamma p.1 * m) ∧
        0 < Nat.card BtypicalK ∧
        Nat.multinomial Finset.univ
            (fun p ↦ MME.DWZTable2Counts.gamma p * m) =
          Nat.multinomial Finset.univ
              (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) *
            Nat.card BtypicalK := by
  classical
  let beta := Σ k : Fin 5, Fin (MME.DWZTable2Counts.alphaZ k * m)
  have halphaSum : ∑ k, MME.DWZTable2Counts.alphaZ k =
      MME.DWZTable2Counts.scale :=
    mme_dwz_table2_integer_counts_exact.2.2.2.2.2.1
  have hcardBeta : Fintype.card beta = MME.DWZTable2Counts.scale * m := by
    simp [beta, Fintype.card_sigma, ← Finset.sum_mul, halphaSum]
  let e : Fin (MME.DWZTable2Counts.scale * m) ≃ beta :=
    Fintype.equivOfCardEq (by simpa using hcardBeta.symm)
  let K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 := fun t => (e t).1
  have hK : ∀ k, Fintype.card {t // K t = k} =
      MME.DWZTable2Counts.alphaZ k * m := by
    intro k
    let eFiber : {t // K t = k} ≃ {b : beta // b.1 = k} :=
      Equiv.subtypeEquiv e (fun _ => by rfl)
    calc
      Fintype.card {t // K t = k} =
          Fintype.card {b : beta // b.1 = k} := Fintype.card_congr eFiber
      _ = Fintype.card (Fin (MME.DWZTable2Counts.alphaZ k * m)) :=
        Fintype.card_congr (Equiv.sigmaSubtype k)
      _ = MME.DWZTable2Counts.alphaZ k * m := Fintype.card_fin _
  have hPush : ∀ k,
      (∑ p : {p : Fin 3 × Fin 3 //
          MME.DWZTable2Counts.coarseOf p = k},
        MME.DWZTable2Counts.gamma p.1 * m) =
        MME.DWZTable2Counts.alphaZ k * m := by
    intro k
    simpa only [Finset.sum_mul] using congrArg (fun n : ℕ => n * m)
      (mme_dwz_table2_gamma_pushforward k)
  have hCount := mme_dwz_lemma6_7_typical_denominator_count
    MME.DWZTable2Counts.coarseOf K
    (fun p ↦ MME.DWZTable2Counts.gamma p * m)
    (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) hK hPush
  refine ⟨K, hK, hCount.1, ?_, hCount.2⟩
  rw [hCount.1]
  exact Finset.prod_pos fun k hk => Nat.multinomial_pos _ _
