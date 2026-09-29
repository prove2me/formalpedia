-- Prove2me | solution 1 for mme_dwz_table2_exact_profile_coarse_Z_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:55:33.058467+00:00
-- url     : https://prove2.me/submissions/ace55b4b-fad3-4449-a89d-6439d7309952

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZExactProfileCoarseZSolution

private def fiberEquiv
    {ι σ κ : Type*} (w : ι → σ) (f : σ → κ) (k : κ) :
    {t : ι // f (w t) = k} ≃
      Σ s : {s : σ // f s = k}, {t : ι // w t = s.1} where
  toFun t := ⟨⟨w t.1, t.2⟩, ⟨t.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    cases ht
    rfl

private theorem fiber_card
    {ι σ κ : Type*} [Fintype ι] [Fintype σ] [Fintype κ]
    [DecidableEq σ] [DecidableEq κ]
    (w : ι → σ) (f : σ → κ) (counts : σ → ℕ)
    (hcounts : ∀ s, Fintype.card {t : ι // w t = s} = counts s)
    (k : κ) :
    Fintype.card {t : ι // f (w t) = k} =
      ∑ s : {s : σ // f s = k}, counts s.1 := by
  rw [Fintype.card_congr (fiberEquiv w f k), Fintype.card_sigma]
  exact Finset.sum_congr rfl fun s _ ↦ hcounts s.1

private theorem component_pushforward (k : Fin 5) :
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

end MME.DWZExactProfileCoarseZSolution

theorem solution
    (m : ℕ) {Position : Type*} [Fintype Position]
    (w : Position → Fin 15)
    (hw : ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m) :
    ∀ z, Fintype.card
        {t : Position // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m := by
  intro z
  calc
    Fintype.card
        {t : Position // MME.DWZSquare.shapeZ (w t) = z} =
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = z},
          MME.DWZTable2Counts.component s.1 * m :=
      MME.DWZExactProfileCoarseZSolution.fiber_card
        w MME.DWZSquare.shapeZ
          (fun s ↦ MME.DWZTable2Counts.component s * m) hw z
    _ = MME.DWZTable2Counts.alphaZ z * m := by
      rw [← Finset.sum_mul,
        MME.DWZExactProfileCoarseZSolution.component_pushforward]
