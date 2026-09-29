-- Prove2me | solution 1 for mme_dwz_table2_first_hash_uniform_xy_degree_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:29:21.449019+00:00
-- url     : https://prove2.me/submissions/4e1b7a50-d658-447f-93ba-81df1e04bedb

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
import Theorems.Thm_mme_dwz_table2_first_hash_x_denominator_lower
import Theorems.Thm_mme_dwz_table2_same_marginal_triple_count_upper_positive

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

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
      (d : ℝ) ≤
        (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 5 *
          (((sourceLength + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) := by
  classical
  dsimp only
  rcases mme_dwz_table2_first_hash_uniform_xy_degree m with
    ⟨d, hXNonempty, hYNonempty, hMNonempty, hd,
      hFX, hFY, hFactorX, hFactorY, hXCount, hYCount,
      hXYCount, _hBX, _hBY⟩
  refine ⟨d, hXNonempty, hYNonempty, hMNonempty, hd,
    hFX, hFY, hFactorX, hFactorY, hXCount, hYCount, hXYCount, ?_⟩
  by_cases hm : m = 0
  · subst m
    let XWord :=
      {I : Fin (MME.DWZTable2Counts.scale * 0) → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} =
          ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
            MME.DWZTable2Counts.component s.1 * 0}
    let MarginalTriple :=
      {w : Fin (MME.DWZTable2Counts.scale * 0) → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} =
              ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
                MME.DWZTable2Counts.component s.1 * 0) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} =
              ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
                MME.DWZTable2Counts.component s.1 * 0) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * 0}
    have hXSub : Subsingleton XWord := ⟨by
      intro I J
      apply Subtype.ext
      funext t
      exact Fin.elim0 t⟩
    have hMSub : Subsingleton MarginalTriple := ⟨by
      intro I J
      apply Subtype.ext
      funext t
      exact Fin.elim0 t⟩
    have hXCard : Nat.card XWord = 1 :=
      @Nat.card_unique XWord hXNonempty hXSub
    have hMCard : Nat.card MarginalTriple = 1 :=
      @Nat.card_unique MarginalTriple hMNonempty hMSub
    have hdOne : d = 1 := by
      change Nat.card MarginalTriple = Nat.card XWord * d at hFactorX
      rw [hMCard, hXCard] at hFactorX
      omega
    subst d
    norm_num
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} =
              ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
                MME.DWZTable2Counts.component s.1 * m) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    have hNum :=
      mme_dwz_table2_same_marginal_triple_count_upper_positive m hmpos
    have hDen := mme_dwz_table2_first_hash_x_denominator_lower m
    dsimp only at hNum hDen
    have hFactorReal :
        (Nat.card MarginalTriple : ℝ) =
          (Nat.card XWord : ℝ) * (d : ℝ) := by
      exact_mod_cast hFactorX
    let EX : ℝ :=
      (m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
        mme_modern_entropyBits
          (mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha)
    let EM : ℝ :=
      (m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
        MME.DWZSquare.maxSameMarginalEntropy
    let PX : ℝ := (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 5
    let PJ : ℝ := (((sourceLength + 1 : ℕ) : ℝ)) ^ 15
    have hIntermediate : Real.exp EX * (d : ℝ) ≤
        PX * PJ * Real.exp EM := by
      calc
        Real.exp EX * (d : ℝ) ≤
            (PX * (Nat.card XWord : ℝ)) * (d : ℝ) := by
          exact mul_le_mul_of_nonneg_right hDen (by positivity)
        _ = PX * (Nat.card MarginalTriple : ℝ) := by
          rw [hFactorReal]
          ring
        _ ≤ PX * (PJ * Real.exp EM) := by
          exact mul_le_mul_of_nonneg_left hNum (by positivity)
        _ = PX * PJ * Real.exp EM := by ring
    have hRate : EM - EX =
        (m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          (MME.DWZSquare.maxSameMarginalEntropy -
            mme_modern_entropyBits
              (mme_modern_marginal MME.DWZSquare.shapeX
                MME.DWZSquare.alpha)) := by
      dsimp only [EM, EX]
      ring
    rw [← hRate]
    change (d : ℝ) ≤ PX * PJ * Real.exp (EM - EX)
    apply le_of_mul_le_mul_left ?_ (Real.exp_pos EX)
    calc
      Real.exp EX * (d : ℝ) ≤ PX * PJ * Real.exp EM := hIntermediate
      _ = Real.exp EX * (PX * PJ * Real.exp (EM - EX)) := by
        have hExpFactor : Real.exp EM =
            Real.exp EX * Real.exp (EM - EX) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hExpFactor]
        ring
