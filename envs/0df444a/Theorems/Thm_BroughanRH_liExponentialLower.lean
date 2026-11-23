-- Prove2me | Theorems.Thm_BroughanRH_liExponentialLower
-- name    : BroughanRH.liExponentialLower
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:22:28.952785+00:00
-- url     : https://prove2.me/theorems/5d94d919-c021-4575-9779-0367aac2f23c
-- title:
--   Bombieri–Lagarias’s exponential lower bound for the zeta zero sums
-- statement:
--   For every $\varepsilon>0$ there is $C_\varepsilon>0$ such that $\lambda_n\geq-C_\varepsilon e^{\varepsilon n}$ for all positive integers $n$. The real parts of the zero-sum terms are absolutely summable with multiplicities.
--
--   Lean proof using the strict zero-sum criterion:
--
--   ```lean
--   by
--     intro Z ε hε
--     refine ⟨1, by norm_num, ?_⟩
--     intro n hn
--     obtain ⟨hs, hp⟩ := BroughanRH.liZeroSum n hn
--     exact ⟨hs, le_trans (neg_nonpos.mpr (mul_nonneg zero_le_one (Real.exp_pos _).le)) hp.le⟩
--   ```
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 4.16(c), zeta specialization. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem liExponentialLower :
    let Z := {s : ℂ // ConnesRZ.IsCriticalZero s}
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      let u (ρ : Z) : ℝ := (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - (1 - 1/ρ.val)^n).re
      Summable u ∧ -(C * Real.exp (ε * n)) ≤ ∑' ρ : Z, u ρ := by sorry

end BroughanRH
