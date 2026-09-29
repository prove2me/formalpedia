-- Prove2me | solution 1 for mme_dwz_table2_exact_profile_XYZ_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T01:24:04.69738+00:00
-- url     : https://prove2.me/submissions/ca52a00a-9c1e-4ef4-b27a-9ba3b672a57d

import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZExactMarginalTransport

private def composedFiberEquiv
    {ι σ κ : Type*} (w : ι → σ) (f : σ → κ) (k : κ) :
    {t : ι // f (w t) = k} ≃
      Σ s : {s : σ // f s = k}, {t : ι // w t = s.1} where
  toFun t := ⟨⟨w t.1, t.2⟩, ⟨t.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨s, _hs⟩, ⟨t, ht⟩⟩
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

end MME.DWZExactMarginalTransport

theorem solution
    (m : ℕ) {Position : Type*} [Fintype Position]
    (w : Position → Fin 15)
    (hw : ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m) :
    (∀ x, Fintype.card
        {t : Position // MME.DWZSquare.shapeX (w t) = x} =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m) ∧
    (∀ y, Fintype.card
        {t : Position // MME.DWZSquare.shapeY (w t) = y} =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m) ∧
    ∀ z, Fintype.card
        {t : Position // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m := by
  refine ⟨?_, ?_, mme_dwz_table2_exact_profile_coarse_Z_counts m w hw⟩
  · intro x
    exact MME.DWZExactMarginalTransport.composed_fiber_card
      w MME.DWZSquare.shapeX
        (fun s ↦ MME.DWZTable2Counts.component s * m) hw x
  · intro y
    exact MME.DWZExactMarginalTransport.composed_fiber_card
      w MME.DWZSquare.shapeY
        (fun s ↦ MME.DWZTable2Counts.component s * m) hw y
