-- Prove2me | solution 1 for mme_dwz_table2_claim6_8_prime_survival
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T20:35:02.10144+00:00
-- url     : https://prove2.me/submissions/da1c1c40-cf75-459b-9963-82b70f73b762

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_table2_claim6_8_bounded_address_adapter

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
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
      let R : ℝ :=
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
        MME.DWZSquare.shapeX (I.1 (reindex t))
      let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
      (∀ k, Fintype.card {t : Fin sourceLength // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧
        Nonempty Typical ∧
        Function.Injective
          (fun I : Outer ↦ fun t ↦ MME.DWZSquare.shapeX (I.1 t)) ∧
        Nat.multinomial Finset.univ
            (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
          Nat.multinomial Finset.univ
              (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
            Nat.card Outer ∧
        ∀ (retained : Outer) (small : Typical),
          let outerCandidates :=
            Finset.univ.filter
              (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
          ∃ p : ℕ, ∃ hp : p.Prime,
            letI : Fact p.Prime := ⟨hp⟩
            Odd p ∧
              4 < p ∧
              (outerCandidates.card : ℝ) ≤ R ∧
              8 * outerCandidates.card ≤ p ∧
              max 4 (8 * outerCandidates.card) < p ∧
              p ≤ 2 * max 4 (8 * outerCandidates.card) ∧
              (p : ℝ) ≤ max 8 (16 * R) ∧
              ∀ (b0 : ZMod p)
                (bad : (Fin (n + 1) → ZMod p) → Prop)
                [DecidablePred bad],
                let hX : (Fin (n + 1) → ZMod p) →
                    (Fin (n + 1) → Fin 5) → ZMod p :=
                  fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
                let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
                    (Fin (n + 1) → Fin 5) → ZMod p :=
                  fun w0 w C ↦
                    b0 + (2 : ZMod p)⁻¹ *
                      (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
                let conditionedW0 :
                    (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
                  2 * (∑ t,
                    ((addressX retained t).val : ZMod p) * w t) -
                    ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
                (∀ w, bad w →
                  ∃ A ∈ outerCandidates,
                    hX w (addressX A) =
                      hZ (conditionedW0 w) w addressZ) →
                8 * (Finset.univ.filter bad).card ≤
                  Fintype.card (Fin (n + 1) → ZMod p) := by
  classical
  obtain ⟨K, hK, hOuter, hTypical, hInjective, hFactor, hprime⟩ :=
    mme_dwz_table2_compatible_outer_candidate_prime_budget m
  refine ⟨K, ?_⟩
  dsimp only
  refine ⟨hK, hOuter, hTypical, hInjective, hFactor, ?_⟩
  intro retained small
  obtain ⟨candidates, hcandidates, hrate, p, hp, hpodd, h4p,
      hbudget, hlower, hupper, hpRate⟩ := hprime retained small
  have hcandidatesEq : candidates =
      Finset.univ.filter
        (fun A ↦ A ≠ retained ∧
          (∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
            Fintype.card
                {t : Fin (MME.DWZTable2Counts.scale * m) //
                  (if h : MME.DWZSquare.shapeX (A.1 t) = 0 ∨
                      MME.DWZSquare.shapeY (A.1 t) = 0 then
                    Sum.inl ⟨A.1 t, h⟩
                  else
                    Sum.inr (MME.DWZSquare.shapeZ (A.1 t))) = r ∧
                    (small.1 t).1 = a} =
              MME.DWZTable2Cardinality.cellCount m r a)) := by
    ext A
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      hcandidates A
  subst candidates
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpodd, h4p, hrate, hbudget, hlower, hupper, hpRate, ?_⟩
  intro b0 bad _ hcoverage
  exact mme_dwz_table2_claim6_8_bounded_address_adapter
    m hm K hpodd h4p b0 retained small bad hcoverage hbudget
