-- Prove2me | solution 1 for mme_dwz_table2_equation21_combined_prime_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T21:18:06.017811+00:00
-- url     : https://prove2.me/submissions/b6fec57a-b695-4f88-8eaa-0309f692856c

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution (m : ℕ) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    let YWord :=
      {J : Fin sourceLength → Fin 5 //
        ∀ y, Fintype.card {t // J t = y} = alphaY y}
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    let xWord : MarginalTriple → XWord := fun w ↦
      ⟨fun t ↦ MME.DWZSquare.shapeX (w.1 t), w.2.1⟩
    let yWord : MarginalTriple → YWord := fun w ↦
      ⟨fun t ↦ MME.DWZSquare.shapeY (w.1 t), w.2.2.1⟩
    let FixedX : XWord → Type := fun I ↦
      {w : MarginalTriple // xWord w = I}
    let FixedY : YWord → Type := fun J ↦
      {w : MarginalTriple // yWord w = J}
    ∃ d : ℕ,
      Nonempty XWord ∧
      Nonempty YWord ∧
      Nonempty MarginalTriple ∧
      0 < d ∧
      (∀ I : XWord, Nat.card (FixedX I) = d) ∧
      (∀ J : YWord, Nat.card (FixedY J) = d) ∧
      Nat.card MarginalTriple = Nat.card XWord * d ∧
      Nat.card MarginalTriple = Nat.card YWord * d ∧
      Nat.card XWord = Nat.multinomial Finset.univ alphaX ∧
      Nat.card YWord = Nat.multinomial Finset.univ alphaY ∧
      Nat.card XWord = Nat.card YWord ∧
      (∀ I : XWord, 4 * Nat.card (FixedX I) ≤ 8 * d) ∧
      (∀ J : YWord, 4 * Nat.card (FixedY J) ≤ 8 * d) ∧
      ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
        let regionOfShape :
            Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
          if h : MME.DWZSquare.shapeX s = 0 ∨
              MME.DWZSquare.shapeY s = 0 then
            Sum.inl ⟨s, h⟩
          else
            Sum.inr (MME.DWZSquare.shapeZ s)
        let Outer :=
          {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
            (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
            ∀ s, Fintype.card {t // w t = s} =
              MME.DWZTable2Counts.component s * m}
        let Typical :=
          {small : Fin (MME.DWZTable2Counts.scale * m) → Fin 3 × Fin 3 //
            (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
            ∀ p, Fintype.card {t // small t = p} =
              MME.DWZTable2Counts.gamma p * m}
        let Compatible : Outer → Typical → Prop := fun I small ↦
          ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
            Fintype.card
                {t //
                  regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
              MME.DWZTable2Cardinality.cellCount m r a
        let R : ℝ :=
          (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
            (Nat.card Outer : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP)
        (∀ k, Fintype.card {t // K t = k} =
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
          ∀ (retained : Outer) (small₀ : Typical),
            ∃ candidates : Finset Outer,
              (∀ I, I ∈ candidates ↔
                I ≠ retained ∧ Compatible I small₀) ∧
              (candidates.card : ℝ) ≤ R ∧
              let M0 := max 4 (8 * max d candidates.card)
              ∃ p : ℕ,
                p.Prime ∧ Odd p ∧
                4 < p ∧
                8 * d ≤ p ∧
                8 * candidates.card ≤ p ∧
                M0 < p ∧ p ≤ 2 * M0 := by
  classical
  dsimp only
  obtain ⟨d, hXNonempty, hYNonempty, hMarginalNonempty, hd,
      hFixedX, hFixedY, hFactorX, hFactorY, hXCount, hYCount,
      hXYCount, hXCollision, hYCollision⟩ :=
    mme_dwz_table2_first_hash_uniform_xy_degree m
  obtain ⟨K, hK, hOuter, hTypical, hInjective, hOuterFactor,
      hCandidates⟩ :=
    mme_dwz_table2_compatible_outer_candidate_prime_budget m
  refine ⟨d, hXNonempty, hYNonempty, hMarginalNonempty, hd,
    hFixedX, hFixedY, hFactorX, hFactorY, hXCount, hYCount,
    hXYCount, hXCollision, hYCollision, K, hK, hOuter, hTypical,
    hInjective, hOuterFactor, ?_⟩
  intro retained small₀
  obtain ⟨candidates, hmem, hrate, _oldPrime⟩ :=
    hCandidates retained small₀
  refine ⟨candidates, hmem, hrate, ?_⟩
  let M0 : ℕ := max 4 (8 * max d candidates.card)
  change ∃ p : ℕ,
    p.Prime ∧ Odd p ∧
    4 < p ∧
    8 * d ≤ p ∧
    8 * candidates.card ≤ p ∧
    M0 < p ∧ p ≤ 2 * M0
  have hM0 : 2 ≤ M0 := by
    exact (by omega : 2 ≤ 4).trans (le_max_left _ _)
  have hlevel : 4 ≤ M0 := le_max_left _ _
  have hfirst : 8 * d ≤ M0 := by
    have hdmax : d ≤ max d candidates.card := le_max_left _ _
    exact (Nat.mul_le_mul_left 8 hdmax).trans (le_max_right _ _)
  have hcompatible : 8 * candidates.card ≤ M0 := by
    have hCmax : candidates.card ≤ max d candidates.card :=
      le_max_right _ _
    exact (Nat.mul_le_mul_left 8 hCmax).trans (le_max_right _ _)
  obtain ⟨p, hp, hpodd, h4p, hdp, hCp, hM0p, hpM0⟩ :=
    mme_dwz_claim6_8_exists_prime_modulus
      4 d candidates.card M0 hM0 hlevel hfirst hcompatible
  exact ⟨p, hp, hpodd, h4p, hdp, hCp, hM0p, hpM0⟩
