-- Prove2me | Theorems.Thm_DetDLP_stage1_complexity_dominance
-- name    : DetDLP.stage1_complexity_dominance
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:22.533546+00:00
-- url     : https://prove2.me/theorems/20404266-025d-49a8-b25d-535924382698
-- title:
--   Stage I Subexponential Complexity Dominance Bounds
-- statement:
--   Establishes the Stage I asymptotic domination inequalities:
--
--   1. Monotonicity of `mainSpaceBound` and `polyBound` in $C$;
--   2. Factoring time $2^{K b / \sqrt{\log b}} \le \mathrm{mainSpaceBound}(K, b)$;
--   3. $\mathrm{poly}(b) \cdot (m^2 + m g_{\mathrm{ord}}^{1/m}) \le 2^{O(b/(\log b)^{1/4})}$ for $g_{\mathrm{ord}} \le 3p$;
--   4. BTN contraction time `btnTimeBound` fits inside $2^{O(b/(\log b)^{1/4})}$ when $u \le K_u m b$ and $b \le s \le K_s m b$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1 & 3.3 (pp. 7–11)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- Stage I complexity-bound dominance relations (Section 3.1 & 3.3):
(1) Monotonicity of `mainSpaceBound` and `polyBound` in `C`;
(2) Factoring runtime `2^{K b / √(log b)}` fits inside `mainSpaceBound K b`;
(3) Polynomial and factor-base size bounds `poly(b) · (m² + m · gord^{1/m})` fit inside `mainSpaceBound C b`;
(4) Stage I BTN contraction time `btnTimeBound K u s` fits inside `mainSpaceBound C b` when `u ≤ K_u m b` and `b ≤ s ≤ K_s m b`. -/
theorem stage1_complexity_dominance :
    (∀ (C₁ C₂ b : ℕ), C₁ ≤ C₂ →
      mainSpaceBound C₁ b ≤ mainSpaceBound C₂ b ∧ polyBound C₁ b ≤ polyBound C₂ b) ∧
    (∀ (K b : ℕ),
      (2 : ℝ) ^ ((K : ℝ) * (b : ℝ) / Real.sqrt (logSafe (b : ℝ))) ≤ mainSpaceBound K b) ∧
    (∀ (K C_fb : ℕ), ∃ C : ℕ,
      ∀ (p gord : ℕ), 2 ≤ p → gord ≤ 3 * p →
        let b := bitLen p
        let m := blockCount b
        polyBound K b ≤ mainSpaceBound C b ∧
        polyBound K b *
          ((C_fb : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)))) ≤
          mainSpaceBound C b) ∧
    (∀ (K K_u K_s : ℕ), ∃ C : ℕ,
      ∀ (p u s : ℕ), 2 ≤ p →
        let b := bitLen p
        let m := blockCount b
        u ≤ K_u * m * b → b ≤ s → s ≤ K_s * m * b →
        btnTimeBound K u s ≤ mainSpaceBound C b) := by sorry

end DetDLP
