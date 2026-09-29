-- Prove2me | solution 1 for linear_neumann_off_diagonal_frobenius_bernstein_term_absorbed_under_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T17:55:55.334632+00:00
-- url     : https://prove2.me/submissions/35647240-b2b5-46c8-8917-eae83da824a0

import Definitions.Def_linear_neumann_offdiag_bernstein
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

set_option maxHeartbeats 1000000

namespace ProveE33

theorem frob_sqrt_core
    (β L prod N rr mr μ₀ : ℝ)
    (hβ : 2 < β) (hL : 0 ≤ L) (hprod : 0 < prod)
    (hN : 0 < N) (hrr : 0 ≤ rr) (hmr : 0 < mr) (hμ₀ : 0 ≤ μ₀)
    (hprod_le : prod ≤ N ^ 2) :
    Real.sqrt (((β + 2) * L) / (mr / prod)) *
        Real.sqrt (μ₀ * rr / N) ≤
      2 * Real.sqrt ((μ₀ * N * rr * (β * L)) / mr) := by
  have hβpos : 0 < β := by linarith
  have hβ2 : β + 2 ≤ 2 * β := by linarith
  set A : ℝ := ((β + 2) * L) / (mr / prod) with hA
  set B : ℝ := μ₀ * rr / N with hB
  set C : ℝ := (μ₀ * N * rr * (β * L)) / mr with hC
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hAB_le : A * B ≤ 2 * C := by
    rw [hA, hB, hC]
    field_simp [hprod.ne', hN.ne', hmr.ne']
    have hcoeff : (β + 2) * prod ≤ 2 * β * N ^ 2 := by
      calc
        (β + 2) * prod ≤ (2 * β) * prod := by
          exact mul_le_mul_of_nonneg_right hβ2 (le_of_lt hprod)
        _ ≤ (2 * β) * N ^ 2 := by
          exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
        _ = 2 * β * N ^ 2 := by ring
    have hscale : 0 ≤ L * μ₀ * rr := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hscale]
  calc
    Real.sqrt A * Real.sqrt B = Real.sqrt (A * B) := by
      rw [Real.sqrt_mul hA0]
    _ ≤ Real.sqrt (2 * C) := Real.sqrt_le_sqrt hAB_le
    _ ≤ 2 * Real.sqrt C := by
      have h2C0 : 0 ≤ 2 * C := by positivity
      have hsquare : (Real.sqrt (2 * C)) ^ 2 ≤ (2 * Real.sqrt C) ^ 2 := by
        rw [Real.sq_sqrt h2C0]
        rw [mul_pow, Real.sq_sqrt hC0]
        nlinarith [hC0]
      have hleft0 : 0 ≤ Real.sqrt (2 * C) := Real.sqrt_nonneg _
      have hright0 : 0 ≤ 2 * Real.sqrt C := by positivity
      nlinarith [hsquare, hleft0, hright0]
    _ = 2 * Real.sqrt ((μ₀ * N * rr * (β * L)) / mr) := by rw [hC]

end ProveE33

open ProveE33

theorem solution
    (Ctwo Cfro : ℝ) :
    0 < Ctwo → 0 < Cfro →
    ∃ Cfrob : ℝ, 0 < Cfrob ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂))))) ≤
          Cfrob * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  intro hCtwo hCfro
  refine ⟨2 * Ctwo * Cfro, by positivity, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁ _hsample
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hNdef
  set prod : ℝ := (n₁ : ℝ) * (n₂ : ℝ) with hproddef
  set rr : ℝ := (r : ℝ) with hrrdef
  set mr : ℝ := (m : ℝ) with hmrdef
  have hprod_pos : 0 < prod := by
    rw [hproddef]
    positivity
  have hN_pos : 0 < N := by
    rw [hNdef]
    exact_mod_cast lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hrr_nonneg : 0 ≤ rr := by rw [hrrdef]; positivity
  have hμ₀_nonneg : 0 ≤ μ₀ := by linarith
  have hμ₁_nonneg : 0 ≤ μ₁ := by linarith
  have hsqrt_r_nonneg : 0 ≤ Real.sqrt (rr / prod) := Real.sqrt_nonneg _
  have hprod_le : prod ≤ N ^ 2 := by
    rw [hproddef, hNdef]
    have h1 : (n₁ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by
      exact_mod_cast Nat.le_max_left n₁ n₂
    have h2 : (n₂ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by
      exact_mod_cast Nat.le_max_right n₁ n₂
    nlinarith [Nat.cast_nonneg (α := ℝ) n₁,
      Nat.cast_nonneg (α := ℝ) n₂,
      Nat.cast_nonneg (α := ℝ) (max n₁ n₂)]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst m
    rw [hmrdef]
    norm_num
  · have hmr_pos : 0 < mr := by rw [hmrdef]; exact_mod_cast hmpos
    rcases lt_or_ge N 2 with hNlt2 | hNge2
    · have hmax1 : max n₁ n₂ = 1 := by
        have hlt : max n₁ n₂ < 2 := by
          have : (↑(max n₁ n₂) : ℝ) < 2 := by
            rw [← hNdef]
            exact hNlt2
          exact_mod_cast this
        have hge : 1 ≤ max n₁ n₂ := Nat.succ_le_of_lt (lt_of_lt_of_le hn₁ (Nat.le_max_left _ _))
        omega
      have hlog0 : Real.log (↑(max n₁ n₂) : ℝ) = 0 := by
        rw [hmax1]
        norm_num
      have hlogN0 : Real.log N = 0 := by
        rw [hNdef]
        exact hlog0
      rw [hlogN0]
      norm_num
    · have hL_nonneg : 0 ≤ Real.log N := le_of_lt (Real.log_pos (by linarith))
      have hcore :=
        frob_sqrt_core β (Real.log N) prod N rr mr μ₀ hβ hL_nonneg
          hprod_pos hN_pos hrr_nonneg hmr_pos hμ₀_nonneg hprod_le
      have hfactor_nonneg :
          0 ≤ Ctwo * Cfro * μ₁ * Real.sqrt (rr / prod) := by
        positivity
      have hcore' :
          Ctwo * Cfro * μ₁ * Real.sqrt (rr / prod) *
              (Real.sqrt (((β + 2) * Real.log N) / (mr / prod)) *
                Real.sqrt (μ₀ * rr / N)) ≤
            Ctwo * Cfro * μ₁ * Real.sqrt (rr / prod) *
              (2 * Real.sqrt ((μ₀ * N * rr * (β * Real.log N)) / mr)) := by
        exact mul_le_mul_of_nonneg_left hcore hfactor_nonneg
      have hrewrite_left :
          Ctwo *
              (Real.sqrt
                  (((β + 2) * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Cfro * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))))
            =
          Ctwo * Cfro * μ₁ * Real.sqrt (rr / prod) *
              (Real.sqrt (((β + 2) * Real.log N) / (mr / prod)) *
                Real.sqrt (μ₀ * rr / N)) := by
        rw [hNdef, hproddef, hrrdef, hmrdef]
        ring
      have hrewrite_right :
          (2 * Ctwo * Cfro) * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                      (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
            =
          Ctwo * Cfro * μ₁ * Real.sqrt (rr / prod) *
              (2 * Real.sqrt ((μ₀ * N * rr * (β * Real.log N)) / mr)) := by
        rw [hNdef, hproddef, hrrdef, hmrdef]
        ring
      rw [hrewrite_left, hrewrite_right]
      exact hcore'
