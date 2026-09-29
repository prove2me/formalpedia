-- Prove2me | solution 1 for second_order_quadratic_base_entry_prefactor_absorbed_by_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-22T03:34:43.319269+00:00
-- url     : https://prove2.me/submissions/a950337f-9996-4b96-b72b-1b3d6d6702bd

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
open scoped Classical BigOperators
namespace MatrixCompletion
end MatrixCompletion
open MatrixCompletion

set_option maxHeartbeats 1000000 in
theorem solution
    (Cpref Cbase : ℝ) :
    0 < Cpref → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cpref * Cbase *
            |(((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)| *
            μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCpref hCbase
  refine ⟨Cpref * Cbase, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hbound
  -- abbreviations
  set N : ℝ := (n₁ : ℝ) * (n₂ : ℝ) with hN
  set M : ℝ := (↑(max n₁ n₂) : ℝ) with hM
  set p : ℝ := (m : ℝ) / N with hp
  -- basic positivity
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hlampos : (0 : ℝ) < lam := by linarith
  have hβpos : (0 : ℝ) < β := by linarith
  -- M ≥ 1 since max n₁ n₂ ≥ 1
  have hmax_ge : 1 ≤ max n₁ n₂ := le_trans hn₁ (Nat.le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; exact_mod_cast hmax_ge
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  -- RHS is positive
  have hRHSpos : (0 : ℝ) < Cpref * Cbase * Real.rpow lam (-((3 : ℝ) / 2)) := by
    have : (0:ℝ) < Real.rpow lam (-((3:ℝ)/2)) := Real.rpow_pos_of_pos hlampos _
    positivity
  -- The LHS expression name
  set LHS : ℝ := Cpref * Cbase *
      |(p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)| *
        μ₀ ^ 3 * ((r : ℝ) / M) ^ 3 *
        Real.sqrt ((β * M * Real.log M) / p) with hLHS
  -- Corner case m = 0
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- p = 0 ⇒ p⁻¹ = 0
    have hp0 : p = 0 := by rw [hp, hm0]; simp
    have : LHS = 0 := by
      rw [hLHS, hp0]
      simp
    rw [this]
    exact le_of_lt hRHSpos
  -- m ≥ 1
  -- Corner case max = 1 (M = 1 ⇒ log M = 0)
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hmaxlt | hmaxge
  · -- max < 2 and max ≥ 1 ⇒ max = 1
    have hmax1 : max n₁ n₂ = 1 := le_antisymm (Nat.lt_succ_iff.mp hmaxlt) hmax_ge
    have hMeq1 : M = 1 := by rw [hM, hmax1]; norm_num
    have hlogM0 : Real.log M = 0 := by rw [hMeq1]; exact Real.log_one
    have : LHS = 0 := by
      rw [hLHS, hlogM0]
      simp
    rw [this]
    exact le_of_lt hRHSpos
  -- MAIN CASE: m ≥ 1, max ≥ 2
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  -- p > 0
  have hppos : 0 < p := by rw [hp]; positivity
  -- p ≤ 1 : m ≤ n₁ n₂ = N
  have hmN : (m : ℝ) ≤ N := by rw [hN]; exact_mod_cast (by exact_mod_cast hm : m ≤ n₁ * n₂)
  have hp1 : p ≤ 1 := by rw [hp]; exact (div_le_one hNpos).mpr hmN
  have hp0le : 0 ≤ p := le_of_lt hppos
  -- M ≥ 2
  have hM2 : (2 : ℝ) ≤ M := by rw [hM]; exact_mod_cast hmaxge
  -- log M ≥ log 2 > 0
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogMge : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2
  have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by linarith) hlogMge
  -- β * log M ≥ 1
  have hβlogM1 : (1 : ℝ) ≤ β * Real.log M := by nlinarith [hlogMpos, hβpos]
  -- quadratic bound: 0 ≤ 1 - 3p + 3p² ≤ 1
  have hquad_nn : 0 ≤ 1 - 3 * p + 3 * p ^ 2 := by nlinarith [sq_nonneg (p - 1/2), hp0le, hp1]
  have hquad_le : 1 - 3 * p + 3 * p ^ 2 ≤ 1 := by nlinarith [hp0le, hp1, sq_nonneg p]
  -- |1 - 3p + 3p²| ≤ 1
  have habs_quad : |1 - 3 * p + 3 * p ^ 2| ≤ 1 := by
    rw [abs_of_nonneg hquad_nn]; exact hquad_le
  -- N ≤ M²
  have hn₁le : (n₁ : ℝ) ≤ M := by rw [hM]; exact_mod_cast Nat.le_max_left n₁ n₂
  have hn₂le : (n₂ : ℝ) ≤ M := by rw [hM]; exact_mod_cast Nat.le_max_right n₁ n₂
  have hNM2 : N ≤ M ^ 2 := by
    rw [hN]
    calc (n₁ : ℝ) * (n₂ : ℝ) ≤ M * M :=
          mul_le_mul hn₁le hn₂le (le_of_lt hn₂R) (le_of_lt hMpos)
      _ = M ^ 2 := by ring
  -- abbreviations for positivity
  have hpinvpos : 0 < p⁻¹ := inv_pos.mpr hppos
  have hCC : 0 < Cpref * Cbase := mul_pos hCpref hCbase
  -- the sqrt argument is nonneg
  have hsqrtarg_nn : 0 ≤ (β * M * Real.log M) / p := by positivity
  -- Define LHS' replacing abs factor with (p⁻¹)^2
  set LHS' : ℝ := Cpref * Cbase * (p⁻¹) ^ 2 *
      μ₀ ^ 3 * ((r : ℝ) / M) ^ 3 *
      Real.sqrt ((β * M * Real.log M) / p) with hLHS'
  -- LHS ≤ LHS'
  have habs_le : |(p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)| ≤ (p⁻¹) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc (p⁻¹) ^ 2 * |1 - 3 * p + 3 * p ^ 2| ≤ (p⁻¹) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left habs_quad (sq_nonneg _)
      _ = (p⁻¹) ^ 2 := by ring
  have hLHS_le : LHS ≤ LHS' := by
    rw [hLHS, hLHS']
    gcongr
  -- rpow facts
  have hμ₀pos : (0:ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  -- (rpow μ₀ (4/3))^5 = rpow μ₀ (20/3)
  have hμpow5 : (Real.rpow μ₀ ((4:ℝ)/3)) ^ (5:ℕ) = Real.rpow μ₀ ((20:ℝ)/3) := by
    show (μ₀ ^ ((4:ℝ)/3)) ^ (5:ℕ) = μ₀ ^ ((20:ℝ)/3)
    rw [← Real.rpow_natCast (μ₀ ^ ((4:ℝ)/3)) 5, ← Real.rpow_mul (le_of_lt hμ₀pos)]
    norm_num
  have hrpow5 : (Real.rpow (r:ℝ) ((4:ℝ)/3)) ^ (5:ℕ) = Real.rpow (r:ℝ) ((20:ℝ)/3) := by
    show ((r:ℝ) ^ ((4:ℝ)/3)) ^ (5:ℕ) = (r:ℝ) ^ ((20:ℝ)/3)
    rw [← Real.rpow_natCast ((r:ℝ) ^ ((4:ℝ)/3)) 5, ← Real.rpow_mul (le_of_lt hrR)]
    norm_num
  -- μ₀^6 ≤ rpow μ₀ (20/3)
  have hμ6le : μ₀ ^ (6:ℕ) ≤ Real.rpow μ₀ ((20:ℝ)/3) := by
    show μ₀ ^ (6:ℕ) ≤ μ₀ ^ ((20:ℝ)/3)
    rw [← Real.rpow_natCast μ₀ 6]
    apply Real.rpow_le_rpow_of_exponent_le hμ₀
    norm_num
  have hr6le : (r:ℝ) ^ (6:ℕ) ≤ Real.rpow (r:ℝ) ((20:ℝ)/3) := by
    show (r:ℝ) ^ (6:ℕ) ≤ (r:ℝ) ^ ((20:ℝ)/3)
    rw [← Real.rpow_natCast (r:ℝ) 6]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hr)
    norm_num
  -- rpow positivity
  have hμ43pos : (0:ℝ) < Real.rpow μ₀ ((4:ℝ)/3) := Real.rpow_pos_of_pos hμ₀pos _
  have hr43pos : (0:ℝ) < Real.rpow (r:ℝ) ((4:ℝ)/3) := Real.rpow_pos_of_pos hrR _
  have hμ203pos : (0:ℝ) < Real.rpow μ₀ ((20:ℝ)/3) := Real.rpow_pos_of_pos hμ₀pos _
  have hr203pos : (0:ℝ) < Real.rpow (r:ℝ) ((20:ℝ)/3) := Real.rpow_pos_of_pos hrR _
  -- the sample lower bound L
  set L : ℝ := lam * Real.rpow μ₀ ((4:ℝ)/3) * M * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log M)
    with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]; positivity
  have hmL : L ≤ (m : ℝ) := hbound
  -- m^5 ≥ L^5
  have hmL5 : L ^ (5:ℕ) ≤ (m : ℝ) ^ (5:ℕ) := pow_le_pow_left₀ hLnn hmL 5
  -- L^5 expansion
  have hL5 : L ^ (5:ℕ) =
      lam ^ (5:ℕ) * Real.rpow μ₀ ((20:ℝ)/3) * M ^ (5:ℕ) * Real.rpow (r:ℝ) ((20:ℝ)/3)
        * (β * Real.log M) ^ (5:ℕ) := by
    rw [hLdef]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hμpow5, hrpow5]
  -- the polynomial absorption inequality
  have hlam2 : (1:ℝ) ≤ lam ^ (2:ℕ) := one_le_pow₀ hlam
  have hβlog4 : (1:ℝ) ≤ (β * Real.log M) ^ (4:ℕ) := by
    apply one_le_pow₀ hβlogM1
  have hpoly : μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) ≤
      lam ^ (2:ℕ) * Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)
        * (β * Real.log M) ^ (4:ℕ) := by
    have h1 : μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) ≤
        Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3) := by
      apply mul_le_mul hμ6le hr6le (by positivity) (le_of_lt hμ203pos)
    have hcoef : (1:ℝ) ≤ lam ^ (2:ℕ) * (β * Real.log M) ^ (4:ℕ) := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ lam ^ (2:ℕ) * (β * Real.log M) ^ (4:ℕ) :=
            mul_le_mul hlam2 hβlog4 (by norm_num) (by positivity)
    have h2 : Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3) ≤
        lam ^ (2:ℕ) * Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)
          * (β * Real.log M) ^ (4:ℕ) := by
      have hrr : (0:ℝ) < Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3) :=
        mul_pos hμ203pos hr203pos
      calc Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)
            = 1 * (Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)) := by ring
        _ ≤ (lam ^ (2:ℕ) * (β * Real.log M) ^ (4:ℕ))
              * (Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)) :=
            mul_le_mul_of_nonneg_right hcoef (le_of_lt hrr)
        _ = lam ^ (2:ℕ) * Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)
              * (β * Real.log M) ^ (4:ℕ) := by ring
    exact le_trans h1 h2
  -- master inequality in m
  have hmaster : lam ^ (3:ℕ) * M ^ (5:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)
      ≤ (m : ℝ) ^ (5:ℕ) := by
    have hL5expand : lam ^ (3:ℕ) * M ^ (5:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)
        ≤ L ^ (5:ℕ) := by
      rw [hL5]
      set A : ℝ := lam ^ (3:ℕ) * M ^ (5:ℕ) * (β * Real.log M) with hA
      have hpos : (0:ℝ) ≤ A := by rw [hA]; positivity
      have hstep := mul_le_mul_of_nonneg_left hpoly hpos
      calc lam ^ (3:ℕ) * M ^ (5:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)
            = A * (μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)) := by rw [hA]; ring
        _ ≤ A * (lam ^ (2:ℕ) * Real.rpow μ₀ ((20:ℝ)/3) * Real.rpow (r:ℝ) ((20:ℝ)/3)
              * (β * Real.log M) ^ (4:ℕ)) := hstep
        _ = lam ^ (5:ℕ) * Real.rpow μ₀ ((20:ℝ)/3) * M ^ (5:ℕ) * Real.rpow (r:ℝ) ((20:ℝ)/3)
              * (β * Real.log M) ^ (5:ℕ) := by rw [hA]; ring
    linarith [hmL5]
  -- N^5 ≤ M^10
  have hNnn : (0:ℝ) ≤ N := le_of_lt hNpos
  have hN5 : N ^ (5:ℕ) ≤ M ^ (10:ℕ) := by
    have h := pow_le_pow_left₀ hNnn hNM2 5
    calc N ^ (5:ℕ) ≤ (M ^ 2) ^ (5:ℕ) := h
      _ = M ^ (10:ℕ) := by rw [← pow_mul]
  -- the cleared master inequality
  have hMpos5 : (0:ℝ) < M ^ (5:ℕ) := by positivity
  have hlam3pos : (0:ℝ) < lam ^ (3:ℕ) := by positivity
  have hm5pos : (0:ℝ) < (m:ℝ) ^ (5:ℕ) := by positivity
  have hclear : lam ^ (3:ℕ) * (N ^ (5:ℕ) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M))
      ≤ (m:ℝ) ^ (5:ℕ) * M ^ (5:ℕ) := by
    -- from hmaster times M^5, and N^5 ≤ M^10
    have hstep1 : lam ^ (3:ℕ) * M ^ (10:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)
        ≤ (m:ℝ) ^ (5:ℕ) * M ^ (5:ℕ) := by
      have := mul_le_mul_of_nonneg_right hmaster (le_of_lt hMpos5)
      calc lam ^ (3:ℕ) * M ^ (10:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)
            = (lam ^ (3:ℕ) * M ^ (5:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ)) * M ^ (5:ℕ) := by
              rw [show (10:ℕ) = 5 + 5 from rfl, pow_add]; ring
        _ ≤ (m:ℝ) ^ (5:ℕ) * M ^ (5:ℕ) := this
    -- N^5 ≤ M^10
    have hN5coef : lam ^ (3:ℕ) * (N ^ (5:ℕ) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M))
        ≤ lam ^ (3:ℕ) * M ^ (10:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) := by
      have hfac : (0:ℝ) ≤ lam ^ (3:ℕ) * (μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M)) := by
        positivity
      have hstep := mul_le_mul_of_nonneg_left hN5 hfac
      calc lam ^ (3:ℕ) * (N ^ (5:ℕ) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M))
            = lam ^ (3:ℕ) * (μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M)) * N ^ (5:ℕ) := by ring
        _ ≤ lam ^ (3:ℕ) * (μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M)) * M ^ (10:ℕ) := by
              apply mul_le_mul_of_nonneg_left hN5 hfac
        _ = lam ^ (3:ℕ) * M ^ (10:ℕ) * (β * Real.log M) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) := by ring
    linarith [hN5coef, hstep1]
  -- RHS square: (rpow lam (-(3/2)))^2 = (lam^3)⁻¹
  have ht2 : (Real.rpow lam (-((3:ℝ)/2))) ^ (2:ℕ) = (lam ^ (3:ℕ))⁻¹ := by
    show (lam ^ (-((3:ℝ)/2))) ^ (2:ℕ) = (lam ^ (3:ℕ))⁻¹
    rw [← Real.rpow_natCast (lam ^ (-((3:ℝ)/2))) 2, ← Real.rpow_mul (le_of_lt hlampos)]
    rw [show (-((3:ℝ)/2)) * (2:ℕ) = -(3:ℝ) by norm_num]
    rw [Real.rpow_neg (le_of_lt hlampos)]
    norm_num
  -- now: LHS' ≤ RHS via squaring
  have hLHS'nn : 0 ≤ LHS' := by
    rw [hLHS']; positivity
  have hRHSnn : 0 ≤ Cpref * Cbase * Real.rpow lam (-((3:ℝ)/2)) := le_of_lt hRHSpos
  -- LHS'^2 ≤ RHS^2
  have hsq : LHS' ^ (2:ℕ) ≤ (Cpref * Cbase * Real.rpow lam (-((3:ℝ)/2))) ^ (2:ℕ) := by
    -- expand both
    have hsqrt_sq : (Real.sqrt ((β * M * Real.log M) / p)) ^ (2:ℕ)
        = (β * M * Real.log M) / p :=
      Real.sq_sqrt hsqrtarg_nn
    -- LHS'^2 form
    have hLHS'sq : LHS' ^ (2:ℕ) =
        (Cpref * Cbase) ^ (2:ℕ) * (p⁻¹) ^ (4:ℕ) * μ₀ ^ (6:ℕ) * ((r:ℝ)/M) ^ (6:ℕ)
          * ((β * M * Real.log M) / p) := by
      rw [hLHS']
      rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
      rw [hsqrt_sq]
      ring
    have hRHSsq : (Cpref * Cbase * Real.rpow lam (-((3:ℝ)/2))) ^ (2:ℕ)
        = (Cpref * Cbase) ^ (2:ℕ) * (lam ^ (3:ℕ))⁻¹ := by
      rw [mul_pow, ht2]
    rw [hLHS'sq, hRHSsq]
    -- cancel (Cpref*Cbase)^2
    have hCC2pos : (0:ℝ) < (Cpref * Cbase) ^ (2:ℕ) := by positivity
    -- the inner inequality
    have hinner : (p⁻¹) ^ (4:ℕ) * μ₀ ^ (6:ℕ) * ((r:ℝ)/M) ^ (6:ℕ)
        * ((β * M * Real.log M) / p) ≤ (lam ^ (3:ℕ))⁻¹ := by
      have hmRpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos
      -- rewrite LHS in terms of N, m, M (substitute p = m/N)
      have hLHSeq : (p⁻¹) ^ (4:ℕ) * μ₀ ^ (6:ℕ) * ((r:ℝ)/M) ^ (6:ℕ)
          * ((β * M * Real.log M) / p)
          = (N ^ (5:ℕ) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M))
              / ((m:ℝ) ^ (5:ℕ) * M ^ (5:ℕ)) := by
        rw [hp]
        field_simp
      rw [hLHSeq]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (m:ℝ) ^ (5:ℕ) * M ^ (5:ℕ))]
      rw [inv_mul_eq_div, le_div_iff₀ hlam3pos]
      -- goal: (N^5·μ₀^6·r^6·βlogM) * lam^3 ≤ m^5·M^5  (up to assoc/comm)
      calc (N ^ (5:ℕ) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M)) * lam ^ (3:ℕ)
            = lam ^ (3:ℕ) * (N ^ (5:ℕ) * μ₀ ^ (6:ℕ) * (r:ℝ) ^ (6:ℕ) * (β * Real.log M)) := by ring
        _ ≤ (m:ℝ) ^ (5:ℕ) * M ^ (5:ℕ) := hclear
    calc (Cpref * Cbase) ^ (2:ℕ) * (p⁻¹) ^ (4:ℕ) * μ₀ ^ (6:ℕ) * ((r:ℝ)/M) ^ (6:ℕ)
            * ((β * M * Real.log M) / p)
          = (Cpref * Cbase) ^ (2:ℕ) * ((p⁻¹) ^ (4:ℕ) * μ₀ ^ (6:ℕ) * ((r:ℝ)/M) ^ (6:ℕ)
              * ((β * M * Real.log M) / p)) := by ring
      _ ≤ (Cpref * Cbase) ^ (2:ℕ) * (lam ^ (3:ℕ))⁻¹ :=
          mul_le_mul_of_nonneg_left hinner (le_of_lt hCC2pos)
  -- conclude
  have hfinal : LHS' ≤ Cpref * Cbase * Real.rpow lam (-((3:ℝ)/2)) :=
    le_of_pow_le_pow_left₀ (by norm_num) hRHSnn hsq
  exact le_trans hLHS_le hfinal

#print axioms solution
