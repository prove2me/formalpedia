-- Prove2me | solution 1 for mme_CW_q6_primary_hash_sqrt_capacity_common_halving
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T12:19:21.82491+00:00
-- url     : https://prove2.me/submissions/241d404d-2ccd-4d83-8a07-ef2955f23010

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_common_paired_halving
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded

open MME BigOperators Filter

set_option autoImplicit false

/-- The common-halving primary-hash capacity bound.  It is the bounded form of the
same statement (which additionally records `H ≤ 4 ^ N`) with that extra conjunct
dropped. -/
theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        let N : ℕ := 2 * n
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N L G A H,
            ∃ _halving : family.CommonBalancedXYHalving,
              raw ^ (2 * N) *
                  Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
                (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                  ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  obtain ⟨C, hC, hev⟩ :=
    mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨A, H, family, halving, _, hineq⟩ := hn
  exact ⟨A, H, family, halving, hineq⟩
