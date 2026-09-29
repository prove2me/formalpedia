-- Prove2me | solution 1 for mme_dwz_table2_first_hash_x_denominator_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:04:10.629759+00:00
-- url     : https://prove2.me/submissions/5989d6a8-aef9-4c32-9e12-7f9626362168

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZFirstHashDenominator

private theorem table2_component_marginal_x (i : Fin 5) :
    ((∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = i},
        MME.DWZTable2Counts.component s.1 : ℕ) : ℝ) /
        (MME.DWZTable2Counts.scale : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeX
        MME.DWZSquare.alpha i := by
  classical
  rcases mme_dwz_table2_integer_counts_exact with ⟨hcomponent, _⟩
  have hscale : (MME.DWZTable2Counts.scale : ℝ) ≠ 0 := by
    norm_num [MME.DWZTable2Counts.scale]
  unfold mme_modern_marginal
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  apply (div_eq_iff hscale).2
  simpa only [mul_comm] using (hcomponent s.1).symm

theorem proof (m : ℕ) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeX
              MME.DWZSquare.alpha)) ≤
      (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 5 *
        (Nat.card XWord : ℝ) := by
  classical
  dsimp only
  rcases mme_dwz_table2_first_hash_uniform_xy_degree m with
    ⟨_d, hXNonempty, _hYNonempty, _hMNonempty, _hd,
      _hFX, _hFY, _hFactorX, _hFactorY, hXCount, _hYCount,
      _hXY, _hBX, _hBY⟩
  by_cases hm : m = 0
  · subst m
    let XWord :=
      {I : Fin (MME.DWZTable2Counts.scale * 0) → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} =
          ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
            MME.DWZTable2Counts.component s.1 * 0}
    have hXSub : Subsingleton XWord := ⟨by
      intro I J
      apply Subtype.ext
      funext t
      exact Fin.elim0 t⟩
    have hXCard : Nat.card XWord = 1 :=
      @Nat.card_unique XWord hXNonempty hXSub
    simp only [Nat.cast_zero, zero_mul, Nat.mul_zero, Nat.zero_add,
      Nat.cast_one, Real.exp_zero]
    change 1 ≤ (6 * (1 : ℝ)) ^ 5 * (Nat.card XWord : ℝ)
    rw [hXCard]
    norm_num
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    let baseX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1
    have hbaseXSum : ∑ x, baseX x = MME.DWZTable2Counts.scale := by
      rcases mme_dwz_table2_integer_counts_exact with
        ⟨_, _, _, hcomponentSum, _⟩
      calc
        ∑ x, baseX x =
            ∑ x : Fin 5,
              ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
                MME.DWZTable2Counts.component s.1 := by rfl
        _ = ∑ s : Fin 15, MME.DWZTable2Counts.component s := by
          symm
          calc
            ∑ s : Fin 15, MME.DWZTable2Counts.component s =
                ∑ t : Σ x : Fin 5,
                    {s : Fin 15 // MME.DWZSquare.shapeX s = x},
                  MME.DWZTable2Counts.component t.2.1 := by
              symm
              exact
                (Equiv.sum_comp
                  (Equiv.sigmaFiberEquiv MME.DWZSquare.shapeX)
                  MME.DWZTable2Counts.component)
            _ = ∑ x : Fin 5,
                ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
                  MME.DWZTable2Counts.component s.1 :=
              Fintype.sum_sigma _
        _ = MME.DWZTable2Counts.scale := hcomponentSum
    have hbaseXPos : 0 < ∑ x, baseX x := by
      rw [hbaseXSum]
      norm_num [MME.DWZTable2Counts.scale]
    have hbaseXNormalized :
        (fun x ↦ (baseX x : ℝ) /
          (((∑ y, baseX y : ℕ) : ℝ))) =
          mme_modern_marginal MME.DWZSquare.shapeX
            MME.DWZSquare.alpha := by
      funext i
      rw [hbaseXSum]
      exact table2_component_marginal_x i
    have hAlphaXScale :
        (fun x ↦ baseX x * m) = alphaX := by
      funext x
      dsimp only [baseX, alphaX]
      rw [Finset.sum_mul]
    have hLower := mme_dwz_multinomial_entropy_polynomial_lower
      baseX m hmpos hbaseXPos
    rw [hbaseXNormalized, hbaseXSum] at hLower
    have hXCountLocal : Nat.card XWord =
        Nat.multinomial Finset.univ (fun x ↦ baseX x * m) := by
      change Nat.card XWord = Nat.multinomial Finset.univ alphaX at hXCount
      rw [hXCount, hAlphaXScale]
    rw [hXCountLocal]
    rw [show
      (m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha) =
        (m : ℝ) *
          ((MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (mme_modern_marginal MME.DWZSquare.shapeX
                MME.DWZSquare.alpha)) by ring]
    simpa only [Fintype.card_fin] using hLower

end MME.DWZFirstHashDenominator

theorem solution (m : ℕ) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeX
              MME.DWZSquare.alpha)) ≤
      (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 5 *
        (Nat.card XWord : ℝ) :=
  MME.DWZFirstHashDenominator.proof m
