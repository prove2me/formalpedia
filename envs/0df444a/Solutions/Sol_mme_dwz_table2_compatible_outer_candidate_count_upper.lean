-- Prove2me | solution 1 for mme_dwz_table2_compatible_outer_candidate_count_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:47:56.937119+00:00
-- url     : https://prove2.me/submissions/16855e5a-c93d-4652-87f6-b8e7c0e22cc9

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_dwz_table2_equation23_numerator_count
import Theorems.Thm_mme_dwz_table2_gamma_pushforward
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_logAlphaP_integer_identity
import Theorems.Thm_mme_dwz_table2_compatible_incidence_factorization

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZCandidateRatioBound

private theorem multinomial_entropy_upper_all
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp
        ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun i ↦ (w i : ℝ) / (((∑ j, w j : ℕ) : ℝ))))) := by
  by_cases hW : ∑ i, w i = 0
  · have hw : ∀ i, w i = 0 := by
      intro i
      exact Nat.eq_zero_of_le_zero
        ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ i)).trans_eq hW)
    simp [hw, Nat.multinomial]
  · exact mme_dwz_multinomial_entropy_upper w m hm
      (Nat.pos_of_ne_zero hW)

private theorem reverse_rate_positive
    (m : ℕ) (hm : 0 < m) (B : ℕ)
    (hfactor :
      Nat.multinomial Finset.univ
          (fun p ↦ MME.DWZTable2Counts.gamma p * m) =
        Nat.multinomial Finset.univ
            (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) * B) :
    (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (B : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP) := by
  let S : ℕ := MME.DWZTable2Counts.scale
  let Hg : ℝ := mme_modern_entropyBits
    (fun p ↦ (MME.DWZTable2Counts.gamma p : ℝ) / S)
  let Ha : ℝ := mme_modern_entropyBits
    (fun k ↦ (MME.DWZTable2Counts.alphaZ k : ℝ) / S)
  let Hb : ℝ := ∑ s : Fin 15,
    if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
      (MME.DWZTable2Counts.component s : ℝ) *
        mme_modern_entropyBits
          (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
            MME.DWZTable2Counts.component s)
    else 0
  let Hp : ℝ := ∑ k : Fin 5,
    (MME.DWZTable2Counts.plusMass k : ℝ) *
      mme_modern_entropyBits
        (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
          MME.DWZTable2Counts.plusMass k)
  let Eg : ℝ := (m : ℝ) * ((S : ℝ) * Real.log 2 * Hg)
  let Ea : ℝ := (m : ℝ) * ((S : ℝ) * Real.log 2 * Ha)
  let Eb : ℝ := (m : ℝ) * Real.log 2 * Hb
  let Ep : ℝ := (m : ℝ) * Real.log 2 * Hp
  let P : ℝ := (6 * (((S * m + 1 : ℕ) : ℝ))) ^ 9
  let Nb : ℝ := ∏ s : Fin 15,
    if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
      (Nat.multinomial Finset.univ
        (fun r ↦ MME.DWZTable2Counts.split s r * m) : ℝ)
    else 1
  let Ni : ℝ := ∏ k : Fin 5,
    (Nat.multinomial Finset.univ
      (fun r ↦ MME.DWZTable2Counts.plusSplit k r * m) : ℝ)
  let Mg : ℝ := Nat.multinomial Finset.univ
    (fun p ↦ MME.DWZTable2Counts.gamma p * m)
  let Ma : ℝ := Nat.multinomial Finset.univ
    (fun k ↦ MME.DWZTable2Counts.alphaZ k * m)
  rcases mme_dwz_table2_integer_counts_exact with
    ⟨_, _, hsplitSum, _, hgammaSum, halphaSum, hplusSum, _⟩
  have hSpos : 0 < S := by
    norm_num [S, MME.DWZTable2Counts.scale]
  have hgammaLower : Real.exp Eg ≤ P * Mg := by
    have h := mme_dwz_multinomial_entropy_polynomial_lower
      MME.DWZTable2Counts.gamma m hm (by simpa [S, hgammaSum] using hSpos)
    rw [hgammaSum] at h
    simpa only [Eg, Hg, P, Mg, S, Fintype.card_prod,
      Fintype.card_fin, Nat.reduceMul] using h
  have halphaUpper : Ma ≤ Real.exp Ea := by
    have h := mme_dwz_multinomial_entropy_upper
      MME.DWZTable2Counts.alphaZ m hm
        (by simpa [S, halphaSum] using hSpos)
    rw [halphaSum] at h
    simpa only [Ea, Ha, Ma, S] using h
  have hfactorR : Mg = Ma * (B : ℝ) := by
    dsimp only [Mg, Ma]
    exact_mod_cast hfactor
  have hdenLower : Real.exp (Eg - Ea) ≤ P * (B : ℝ) := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos Ea)
    calc
      Real.exp (Eg - Ea) * Real.exp Ea = Real.exp Eg := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ P * Mg := hgammaLower
      _ = P * (Ma * (B : ℝ)) := by rw [hfactorR]
      _ ≤ P * (Real.exp Ea * (B : ℝ)) := by
        gcongr
      _ = (P * (B : ℝ)) * Real.exp Ea := by ring
  have hboundaryLocal (s : Fin 15) :
      (Nat.multinomial Finset.univ
          (fun r ↦ MME.DWZTable2Counts.split s r * m) : ℝ) ≤
        Real.exp
          ((m : ℝ) *
            ((MME.DWZTable2Counts.component s : ℝ) * Real.log 2 *
              mme_modern_entropyBits
                (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                  MME.DWZTable2Counts.component s))) := by
    have h := multinomial_entropy_upper_all
      (MME.DWZTable2Counts.split s) m hm
    rw [hsplitSum s] at h
    simpa only using h
  have hinteriorLocal (k : Fin 5) :
      (Nat.multinomial Finset.univ
          (fun r ↦ MME.DWZTable2Counts.plusSplit k r * m) : ℝ) ≤
        Real.exp
          ((m : ℝ) *
            ((MME.DWZTable2Counts.plusMass k : ℝ) * Real.log 2 *
              mme_modern_entropyBits
                (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
                  MME.DWZTable2Counts.plusMass k))) := by
    have h := multinomial_entropy_upper_all
      (MME.DWZTable2Counts.plusSplit k) m hm
    rw [hplusSum k] at h
    simpa only using h
  have hEbSum : Eb = ∑ s : Fin 15,
      if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
        (m : ℝ) *
          ((MME.DWZTable2Counts.component s : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                MME.DWZTable2Counts.component s))
      else 0 := by
    dsimp only [Eb, Hb]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> ring
  have hEpSum : Ep = ∑ k : Fin 5,
      (m : ℝ) *
        ((MME.DWZTable2Counts.plusMass k : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
              MME.DWZTable2Counts.plusMass k)) := by
    dsimp only [Ep, Hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hboundary : Nb ≤ Real.exp Eb := by
    rw [hEbSum, Real.exp_sum]
    dsimp only [Nb]
    apply Finset.prod_le_prod
    · intro s hs
      positivity
    · intro s hs
      by_cases hb :
          MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0
      · simpa only [hb, if_true] using hboundaryLocal s
      · simp only [hb, if_false, Real.exp_zero, le_refl]
  have hinterior : Ni ≤ Real.exp Ep := by
    rw [hEpSum, Real.exp_sum]
    dsimp only [Ni]
    apply Finset.prod_le_prod
    · intro k hk
      positivity
    · intro k hk
      exact hinteriorLocal k
  have hnumeratorCard :
      (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) =
        Nb * Ni := by
    rw [mme_dwz_table2_equation23_numerator_count]
    simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_ite, Nat.cast_one, Nb, Ni]
  have hnumerator :
      (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) ≤
        Real.exp (Eb + Ep) := by
    rw [hnumeratorCard, Real.exp_add]
    have hNiNonneg : 0 ≤ Ni := by
      dsimp only [Ni]
      exact Finset.prod_nonneg fun k hk ↦ Nat.cast_nonneg _
    exact mul_le_mul hboundary hinterior hNiNonneg (Real.exp_nonneg Eb)
  have hlog :
      (S : ℝ) * MME.DWZSquare.logAlphaP =
        (S : ℝ) * Ha - (S : ℝ) * Hg + Hb + Hp := by
    simpa only [S, Ha, Hg, Hb, Hp] using
      mme_dwz_table2_logAlphaP_integer_identity
  have hrate :
      (m : ℝ) * (S : ℝ) * Real.log 2 * MME.DWZSquare.logAlphaP =
        Ea - Eg + Eb + Ep := by
    rw [show (m : ℝ) * (S : ℝ) * Real.log 2 *
        MME.DWZSquare.logAlphaP =
      (m : ℝ) * Real.log 2 *
        ((S : ℝ) * MME.DWZSquare.logAlphaP) by ring, hlog]
    dsimp only [Ea, Eg, Eb, Ep]
    ring
  change (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) ≤
    P * (B : ℝ) * Real.exp
      ((m : ℝ) * (S : ℝ) * Real.log 2 * MME.DWZSquare.logAlphaP)
  rw [hrate]
  calc
    (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) ≤
        Real.exp (Eb + Ep) := hnumerator
    _ = Real.exp (Eg - Ea) * Real.exp (Ea - Eg + Eb + Ep) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (P * (B : ℝ)) * Real.exp (Ea - Eg + Eb + Ep) := by
      gcongr

private theorem reverse_rate
    (m : ℕ) (B : ℕ)
    (hfactor :
      Nat.multinomial Finset.univ
          (fun p ↦ MME.DWZTable2Counts.gamma p * m) =
        Nat.multinomial Finset.univ
            (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) * B) :
    (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (B : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP) := by
  by_cases hm : m = 0
  · subst m
    have hB : B = 1 := by
      simpa [Nat.multinomial] using hfactor.symm
    subst B
    rw [mme_dwz_table2_equation23_numerator_count]
    simp [Nat.multinomial]
    norm_num
  · exact reverse_rate_positive m (Nat.pos_of_ne_zero hm) B hfactor

private def regionOfShape :
    Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
  if h : MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
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

private theorem candidate_count_upper
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k, Fintype.card {t : Position // K t = k} =
      MME.DWZTable2Counts.alphaZ k * m)
    (small₀ : Typical m K) :
    (Nat.card {I : Outer m K // Compatible m K I small₀} : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.card (Outer m K) : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP) := by
  classical
  have hPush : ∀ k : Fin 5,
      (∑ p : {p : Fin 3 × Fin 3 //
          MME.DWZTable2Counts.coarseOf p = k},
        MME.DWZTable2Counts.gamma p.1 * m) =
        MME.DWZTable2Counts.alphaZ k * m := by
    intro k
    rw [← Finset.sum_mul, mme_dwz_table2_gamma_pushforward]
  have hCount := mme_dwz_lemma6_7_typical_denominator_count
    MME.DWZTable2Counts.coarseOf K
    (fun p ↦ MME.DWZTable2Counts.gamma p * m)
    (fun k ↦ MME.DWZTable2Counts.alphaZ k * m)
    hK hPush
  have hrate :
      (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) ≤
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card (Typical m K) : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP) := by
    exact reverse_rate m (Nat.card (Typical m K)) hCount.2
  have hinc := mme_dwz_table2_compatible_incidence_factorization m K small₀
  have hincR :
      (Nat.card (Typical m K) : ℝ) *
          (Nat.card {I : Outer m K // Compatible m K I small₀} : ℝ) =
        (Nat.card (Outer m K) : ℝ) *
          (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) := by
    exact_mod_cast hinc
  have hTypicalPosN : 0 < Nat.card (Typical m K) :=
    Finite.card_pos_iff.mpr ⟨small₀⟩
  have hTypicalPosR : (0 : ℝ) < Nat.card (Typical m K) := by
    exact_mod_cast hTypicalPosN
  apply le_of_mul_le_mul_left _ hTypicalPosR
  calc
    (Nat.card (Typical m K) : ℝ) *
          (Nat.card {I : Outer m K // Compatible m K I small₀} : ℝ) =
        (Nat.card (Outer m K) : ℝ) *
          (Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) : ℝ) :=
      hincR
    _ ≤ (Nat.card (Outer m K) : ℝ) *
        ((6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card (Typical m K) : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)) := by
      exact mul_le_mul_of_nonneg_left hrate (by positivity)
    _ = (Nat.card (Typical m K) : ℝ) *
        ((6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card (Outer m K) : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)) := by
      ring

end MME.DWZCandidateRatioBound

open MME.DWZCandidateRatioBound

theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k, Fintype.card {t : Position // K t = k} =
      MME.DWZTable2Counts.alphaZ k * m) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Position → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Position // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    ∀ small₀ : Typical,
      (Nat.card {I : Outer // Compatible I small₀} : ℝ) ≤
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP) := by
  classical
  change ∀ small₀ : Typical m K,
    (Nat.card {I : Outer m K // Compatible m K I small₀} : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.card (Outer m K) : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP)
  intro small₀
  exact candidate_count_upper m K hK small₀
