-- Prove2me | solution 1 for mme_dwz_square_equation25_cofinal_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:20:29.350563+00:00
-- url     : https://prove2.me/submissions/78e8190f-0125-4c5b-8534-747282b4c2e2

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_square_equation25_finite_extraction_sqrt_loss
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss

open MME BigOperators Filter
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < squareRate tau) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((sixSymmetrization
              (TensorObj.kron (CWObj K 6) (CWObj K 6))).kronPow (s n)) ∧
          (V ^ (6 : ℕ)) ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  let s : ℕ → ℕ := fun m => MME.DWZTable2Counts.scale * m
  have hs : Tendsto s atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro n
    refine ⟨n, fun m hm => ?_⟩
    calc
      n ≤ m := hm
      _ = 1 * m := (one_mul m).symm
      _ ≤ MME.DWZTable2Counts.scale * m := by
        apply Nat.mul_le_mul_right
        norm_num [MME.DWZTable2Counts.scale]
  obtain ⟨C, hC, hextract⟩ :=
    mme_dwz_square_equation25_finite_extraction_sqrt_loss
      (K := K) tau htau
  have hpow :
      V ^ (6 : ℕ) < (squareRate tau) ^ (6 : ℕ) :=
    pow_lt_pow_left₀ hVlt hV (by norm_num)
  have habsorb :=
    mme_strict_pow_absorbs_sqrt_exp_loss
      (V ^ (6 : ℕ)) ((squareRate tau) ^ (6 : ℕ)) C
      (pow_nonneg hV 6) hpow hC
  have habsorb' :
      ∀ᶠ m : ℕ in atTop,
        (V ^ (6 : ℕ)) ^ (s m) ≤
          ((squareRate tau) ^ (6 : ℕ)) ^ (s m) *
            Real.exp
              (-C * Real.sqrt (((s m + 1 : ℕ) : ℝ))) :=
    hs.eventually habsorb
  refine ⟨s, fun _ => 0, hs, tendsto_const_nhds, ?_⟩
  filter_upwards [hextract, habsorb'] with m hm hdom
  obtain ⟨k, a, b, c, hrestrict, hrate⟩ := hm
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simpa [s] using hdom.trans hrate
