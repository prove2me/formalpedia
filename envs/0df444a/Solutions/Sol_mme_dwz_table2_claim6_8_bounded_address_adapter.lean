-- Prove2me | solution 1 for mme_dwz_table2_claim6_8_bounded_address_adapter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T20:07:17.815695+00:00
-- url     : https://prove2.me/submissions/557a4f00-5c36-4b35-b83f-0e0ecb694a4c

import Theorems.Thm_mme_dwz_claim6_8_outer_candidates_survive
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

open BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem shape_eq_of_shapeX_shapeZ_eq {s t : Fin 15}
    (hx : MME.DWZSquare.shapeX s = MME.DWZSquare.shapeX t)
    (hz : MME.DWZSquare.shapeZ s = MME.DWZSquare.shapeZ t) :
    s = t := by
  fin_cases s <;> fin_cases t <;>
    simp_all [MME.DWZSquare.shapeX, MME.DWZSquare.shapeZ]

theorem solution
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hlevel : 4 < p) (b0 : ZMod p) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let n := sourceLength - 1
    let reindex : Fin (n + 1) ≃ Fin sourceLength :=
      finCongr (by
        dsimp only [n, sourceLength]
        exact Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Fin sourceLength → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Fin sourceLength // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Fin sourceLength → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ q, Fintype.card {t : Fin sourceLength // small t = q} =
          MME.DWZTable2Counts.gamma q * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Fin sourceLength //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
      MME.DWZSquare.shapeX (I.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
    ∀ (retained : Outer) (small : Typical)
      (bad : (Fin (n + 1) → ZMod p) → Prop) [DecidablePred bad],
      let outerCandidates :=
        Finset.univ.filter
          (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
      let hX : (Fin (n + 1) → ZMod p) →
          (Fin (n + 1) → Fin 5) → ZMod p :=
        fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
      let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
          (Fin (n + 1) → Fin 5) → ZMod p :=
        fun w0 w C ↦
          b0 + (2 : ZMod p)⁻¹ *
            (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
      let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
        fun w ↦
          2 * (∑ t, ((addressX retained t).val : ZMod p) * w t) -
            ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
      (∀ w, bad w →
        ∃ A ∈ outerCandidates,
          hX w (addressX A) = hZ (conditionedW0 w) w addressZ) →
      8 * outerCandidates.card ≤ p →
      8 * (Finset.univ.filter bad).card ≤
        Fintype.card (Fin (n + 1) → ZMod p) := by
  classical
  dsimp only
  intro retained small bad _ hcoverage hbudget
  let sourceLength := MME.DWZTable2Counts.scale * m
  let n := sourceLength - 1
  have hsourceLength : n + 1 = sourceLength := by
    dsimp only [n, sourceLength]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm)))
  let reindex : Fin (n + 1) ≃ Fin sourceLength := finCongr hsourceLength
  let Outer :=
    {w : Fin sourceLength → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Fin sourceLength // w t = s} =
        MME.DWZTable2Counts.component s * m}
  let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
    MME.DWZSquare.shapeX (I.1 (reindex t))
  have haddressX : Function.Injective addressX := by
    intro I J hIJ
    apply Subtype.ext
    funext u
    apply shape_eq_of_shapeX_shapeZ_eq
    · have hu := congrFun hIJ (reindex.symm u)
      simpa only [addressX, Equiv.apply_symm_apply] using hu
    · exact (I.2.1 u).trans (J.2.1 u).symm
  apply mme_dwz_claim6_8_outer_candidates_survive
    hpodd hlevel b0 addressX haddressX retained
      (fun t ↦ K (reindex t))
      (fun I ↦
        ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
          Fintype.card
              {t : Fin sourceLength //
                (if h : MME.DWZSquare.shapeX (I.1 t) = 0 ∨
                    MME.DWZSquare.shapeY (I.1 t) = 0 then
                  Sum.inl ⟨I.1 t, h⟩
                else
                  Sum.inr (MME.DWZSquare.shapeZ (I.1 t))) = r ∧
                  (small.1 t).1 = a} =
            MME.DWZTable2Cardinality.cellCount m r a)
      bad
  · exact hcoverage
  · exact hbudget
