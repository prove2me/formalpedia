-- Prove2me | solution 1 for mme_dwz_table2_compatible_outer_candidate_prime_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T20:17:40.852714+00:00
-- url     : https://prove2.me/submissions/22e69094-2d41-4b45-8591-5f9f6d860f7c

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_count_upper
import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2PrimeBudget

private def regionOfShape :
    Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
  if h : MME.DWZSquare.shapeX s = 0 ∨
      MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private abbrev Outer
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :=
  {w : Position → Fin 15 //
    (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
    ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m}

private abbrev Typical
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :=
  {small : Position → Fin 3 × Fin 3 //
    (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
    ∀ p, Fintype.card {t : Position // small t = p} =
      MME.DWZTable2Counts.gamma p * m}

private def Compatible
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (I : Outer m K) (small : Typical m K) : Prop :=
  ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position //
          regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
      MME.DWZTable2Cardinality.cellCount m r a

private noncomputable def rateBound
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) : ℝ :=
  (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
    (Nat.card (Outer m K) : ℝ) *
    Real.exp
      ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
        MME.DWZSquare.logAlphaP)

private theorem typical_nonempty
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k, Fintype.card {t : Position // K t = k} =
      MME.DWZTable2Counts.alphaZ k * m) :
    Nonempty (Typical m K) := by
  classical
  have hPush : ∀ k : Fin 5,
      (∑ p : {p : Fin 3 × Fin 3 //
          MME.DWZTable2Counts.coarseOf p = k},
        MME.DWZTable2Counts.gamma p.1 * m) =
        MME.DWZTable2Counts.alphaZ k * m := by
    intro k
    simpa only [Finset.sum_mul] using congrArg (fun n : ℕ ↦ n * m)
      (mme_dwz_table2_gamma_pushforward k)
  have hCount := mme_dwz_lemma6_7_typical_denominator_count
    MME.DWZTable2Counts.coarseOf K
    (fun p ↦ MME.DWZTable2Counts.gamma p * m)
    (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) hK hPush
  have hpos : 0 < Nat.card (Typical m K) := by
    rw [hCount.1]
    exact Finset.prod_pos fun k hk ↦ Nat.multinomial_pos _ _
  exact (Nat.card_pos_iff.mp hpos).1

private theorem candidate_prime_budget
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k, Fintype.card {t : Position // K t = k} =
      MME.DWZTable2Counts.alphaZ k * m)
    (retained : Outer m K) (small₀ : Typical m K) :
    let R := rateBound m K
    ∃ candidates : Finset (Outer m K),
      (∀ I, I ∈ candidates ↔
        I ≠ retained ∧ Compatible m K I small₀) ∧
      (candidates.card : ℝ) ≤ R ∧
        ∃ p : ℕ,
          p.Prime ∧ Odd p ∧
          4 < p ∧
          8 * candidates.card ≤ p ∧
          max 4 (8 * candidates.card) < p ∧
          p ≤ 2 * max 4 (8 * candidates.card) ∧
          (p : ℝ) ≤ max 8 (16 * R) := by
  classical
  let candidates :=
    @Finset.filter (Outer m K)
      (fun I : Outer m K ↦
        I ≠ retained ∧ Compatible m K I small₀)
      (fun I ↦ Classical.propDecidable
        (I ≠ retained ∧ Compatible m K I small₀)) Finset.univ
  let all :=
    @Finset.filter (Outer m K)
      (fun I : Outer m K ↦ Compatible m K I small₀)
      (fun I ↦ Classical.propDecidable (Compatible m K I small₀))
      Finset.univ
  let R := rateBound m K
  have hcandidates : ∀ I, I ∈ candidates ↔
      I ≠ retained ∧ Compatible m K I small₀ := by
    intro I
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsubset : candidates ⊆ all := by
    intro I hI
    have hI' := (hcandidates I).mp hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ I, hI'.2⟩
  have hallCard : all.card =
      Nat.card {I : Outer m K // Compatible m K I small₀} := by
    change (Finset.univ.filter
      (fun I : Outer m K ↦ Compatible m K I small₀)).card = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardN : candidates.card ≤
      Nat.card {I : Outer m K // Compatible m K I small₀} := by
    rw [← hallCard]
    exact Finset.card_le_card hsubset
  have hcardR : (candidates.card : ℝ) ≤
      Nat.card {I : Outer m K // Compatible m K I small₀} := by
    exact_mod_cast hcardN
  have hAllRate :
      (Nat.card {I : Outer m K // Compatible m K I small₀} : ℝ) ≤ R := by
    exact
      (mme_dwz_table2_compatible_outer_candidate_count_upper m K hK small₀)
  have hrate : (candidates.card : ℝ) ≤ R := hcardR.trans hAllRate
  let C : ℕ := candidates.card
  let M0 : ℕ := max 4 (8 * C)
  have hM0 : 2 ≤ M0 := by
    dsimp only [M0]
    omega
  have hlevel : 4 ≤ M0 := by
    exact le_max_left _ _
  have hfirst : 8 * 0 ≤ M0 := by omega
  have hcompatible : 8 * C ≤ M0 := by
    exact le_max_right _ _
  obtain ⟨p, hp, hpodd, h4p, _hfirstp, hCp, hM0p, hpM0⟩ :=
    mme_dwz_claim6_8_exists_prime_modulus
      4 0 C M0 hM0 hlevel hfirst hcompatible
  have hpRate : (p : ℝ) ≤ max 8 (16 * R) := by
    by_cases hC : C = 0
    · have hp8 : p ≤ 8 := by
        dsimp only [M0] at hpM0
        omega
      have hp8R : (p : ℝ) ≤ 8 := by exact_mod_cast hp8
      exact hp8R.trans (le_max_left _ _)
    · have hCpos : 0 < C := Nat.pos_of_ne_zero hC
      have hp16 : p ≤ 16 * C := by
        dsimp only [M0] at hpM0
        omega
      have hp16R : (p : ℝ) ≤ 16 * (C : ℝ) := by
        exact_mod_cast hp16
      have hCR : (C : ℝ) ≤ R := by
        simpa only [C] using hrate
      calc
        (p : ℝ) ≤ 16 * (C : ℝ) := hp16R
        _ ≤ 16 * R := by gcongr
        _ ≤ max 8 (16 * R) := le_max_right _ _
  refine ⟨candidates, hcandidates, hrate, p, hp, hpodd, h4p,
    ?_, ?_, ?_, hpRate⟩
  · simpa only [C] using hCp
  · simpa only [M0, C] using hM0p
  · simpa only [M0, C] using hpM0

end MME.DWZTable2PrimeBudget

open MME.DWZTable2PrimeBudget

/-- The concrete Table-2 compatible competitors have a zero-safe odd prime
modulus whose finite size retains their explicit entropy-rate upper bound. -/
theorem solution (m : ℕ) :
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
              ∃ p : ℕ,
                p.Prime ∧ Odd p ∧
                4 < p ∧
                8 * candidates.card ≤ p ∧
                max 4 (8 * candidates.card) < p ∧
                p ≤ 2 * max 4 (8 * candidates.card) ∧
                (p : ℝ) ≤ max 8 (16 * R) := by
  classical
  obtain ⟨K, hK, hOuter, _hHist, _hPointwise, hInjective,
      _hOuterCard, hFactor⟩ :=
    mme_dwz_table2_matchable_outer_family_component_words m
  refine ⟨K, hK, hOuter, typical_nonempty m K hK, hInjective, hFactor, ?_⟩
  intro retained small₀
  exact candidate_prime_budget m K hK retained small₀
