-- Prove2me | solution 1 for mme_CW_q6_coupled_raw_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:04:55.302944+00:00
-- url     : https://prove2.me/submissions/d6da3269-5b59-4e99-86be-6171e4c6ec11

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_mme_CW_q6_coupled_exact_floor_pruning
import Theorems.Thm_mme_CW_q6_primary_hash_outer_family_cyclic_value_below_quarter_root
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root

open MME BigOperators Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V := by
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let loss : ℕ → ℝ := fun N =>
    (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
  have hcast :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hsqrt :
      Tendsto (fun N : ℕ => Real.sqrt (((N + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hsqrt_sqrt :
      Tendsto
        (fun N : ℕ => Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hsqrt
  have hloss : Tendsto loss atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hsqrt_sqrt
  have hneg_half :
      Tendsto (fun N : ℕ => -(loss N / 2)) atTop (nhds 0) := by
    simpa only [zero_div, neg_zero] using (hloss.div_const (2 : ℝ)).neg
  have hexp :
      Tendsto (fun N : ℕ => Real.exp (-(loss N / 2))) atTop (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hneg_half
    rw [Real.exp_zero] at h
    exact h
  have hscaled :
      Tendsto (fun N : ℕ => raw * Real.exp (-(loss N / 2)))
        atTop (nhds raw) := by
    simpa only [mul_one] using tendsto_const_nhds.mul hexp
  have hbase : ∀ᶠ N : ℕ in atTop,
      V < raw * Real.exp (-(loss N / 2)) :=
    hscaled.eventually_const_lt (by simpa only [raw] using hVlt)
  have hprune := mme_CW_q6_coupled_exact_floor_pruning tau htau
  have hfamily :=
    mme_CW_q6_primary_hash_outer_family_cyclic_value_below_quarter_root
      (K := K) tau htau
  have hresult : ∀ᶠ N : ℕ in atTop,
      HasTauValueAtLeast
        (cyclicSymmetrization (coupledObj K 6)) tau V := by
    filter_upwards [hprune, hfamily, hbase, eventually_gt_atTop 0]
      with N hpruneN hfamilyN hbaseN hNpos
    dsimp only at hpruneN hfamilyN
    have hpower_base :
        V ^ (2 * N) <
          (raw * Real.exp (-(loss N / 2))) ^ (2 * N) := by
      exact pow_lt_pow_left₀ hbaseN hV (by omega)
    have hpowered :
        HasTauValueAtLeast
          (cyclicSymmetrization ((coupledObj K 6).kronPow (2 * N)))
          tau (V ^ (2 * N)) := by
      apply hfamilyN hpruneN (V ^ (2 * N)) (pow_nonneg hV _)
      simpa only [raw, loss] using hpower_base
    have hiso :=
      mme_cyclicSymmetrization_kronPow_isomorphic
        (coupledObj K 6) (2 * N)
    have hpow_of_cyclic :
        HasTauValueAtLeast
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N))
          tau (V ^ (2 * N)) :=
      mme_HasTauValueAtLeast_mono_restrict hiso.2 hpowered
    exact mme_HasTauValueAtLeast_kronPow_root
      (cyclicSymmetrization (coupledObj K 6)) tau V (2 * N)
      (by omega) hV hpow_of_cyclic
  exact hresult.exists.choose_spec
