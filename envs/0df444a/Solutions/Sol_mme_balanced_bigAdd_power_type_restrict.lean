-- Prove2me | solution 1 for mme_balanced_bigAdd_power_type_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:16:21.022394+00:00
-- url     : https://prove2.me/submissions/49863b3e-e525-46b6-a824-daec0f29b568

import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K]
    {n r : ℕ} (X : Fin n → TensorObj K 3) (hn : 0 < n) :
    let R : ℕ := n * r
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin n // ∀ p,
          Fintype.card {j // w j = p} = r}
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin W =>
        TensorObj.kronFin n (fun p => (X p).kronPow r)))
      ((TensorObj.bigAdd X).kronPow R) := by
  classical
  dsimp only
  let R : ℕ := n * r
  let Balanced :=
    {w : Fin R → Fin n // ∀ p,
      Fintype.card {j // w j = p} = r}
  let W : ℕ := Nat.card Balanced
  let x : Fin n → TensorQ K 3 := fun p => TensorQ.toQ (X p)
  let wordTerm : (Fin R → Fin n) → TensorQ K 3 :=
    fun w => ∏ j, x (w j)
  let common : TensorQ K 3 := ∏ p, x p ^ r
  let S : Finset (Fin R → Fin n) :=
    Finset.univ.filter
      (fun w => ∀ p, Fintype.card {j // w j = p} = r)
  let P := TensorQ.tensorStrassen K 3 (by omega)
  letI : Preorder (TensorQ K 3) := P.toPreorder
  letI : AddLeftMono (TensorQ K 3) :=
    ⟨fun a b c hbc => by
      simpa [add_comm] using P.add_right b c hbc a⟩
  have hword : ∀ w : Balanced,
      wordTerm w.1 = common := by
    intro w
    dsimp only [wordTerm, common]
    rw [← Finset.prod_fiberwise' Finset.univ w.1 x]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [Finset.prod_const]
    congr 1
    rw [← Fintype.card_subtype]
    exact w.2 p
  have hbalanced_sum :
      (∑ w : Balanced, wordTerm w.1) =
        ∑ w ∈ S, wordTerm w := by
    dsimp only [S, Balanced]
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp
  have htarget :
      (∑ _ : Fin W, common) = ∑ w : Balanced, wordTerm w.1 := by
    rw [show W = Fintype.card Balanced by
      simpa [W] using (Nat.card_eq_fintype_card :
        Nat.card Balanced = Fintype.card Balanced)]
    simp_rw [hword]
    simp
  have hselect :
      P.le
        (∑ w ∈ S, wordTerm w)
        (∑ w : Fin R → Fin n, wordTerm w) := by
    dsimp only [S]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro w _hw _hnot
      exact P.zero_le (wordTerm w)
  rw [← TensorQ.le_toQ]
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_kronPow,
    TensorQ.toQ_bigAdd]
  simp_rw [mme_toQ_kronFin, TensorQ.toQ_kronPow]
  change P.le (∑ _ : Fin W, common)
    ((∑ p, x p) ^ R)
  rw [htarget, hbalanced_sum, Fintype.sum_pow]
  exact hselect
