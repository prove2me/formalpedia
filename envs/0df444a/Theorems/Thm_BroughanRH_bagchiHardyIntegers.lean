-- Prove2me | Theorems.Thm_BroughanRH_bagchiHardyIntegers
-- name    : BroughanRH.bagchiHardyIntegers
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:27.957668+00:00
-- url     : https://prove2.me/theorems/7d8eccf4-96cd-4d7b-b454-7e05a1964ae2
-- title:
--   Bagchi’s Hardy-space approximation by reciprocal integers
-- statement:
--   In the Hardy space on $\operatorname{Re}s>1/2$, the closed linear span of $G_k(s)=(k^{-s}-1/k)\zeta(s)/s$ for positive integers $k$ contains $s\mapsto1/s$. The formula uses the removable value at $s=1$. [Source](https://arxiv.org/abs/math/0607733).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §3.4 (Bagchi, Thm. 2(ii)). https://arxiv.org/abs/math/0607733

import Mathlib

namespace BroughanRH

theorem bagchiHardyIntegers :
    let G (k : ℕ) (s : ℂ) : ℂ := if s = 1 then -(Real.log k : ℂ)/k
      else ((k : ℂ)^(-s) - (k : ℂ)⁻¹) * riemannZeta s / s
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      ∀ σ : ℝ, 1/2 < σ →
        let err (t : ℝ) := let s := (σ : ℂ) + (t : ℂ)*Complex.I
                           ‖s⁻¹ - ∑ j, a j * G (j.val + 1 : ℕ) s‖^2
        MeasureTheory.Integrable err ∧ (∫ t : ℝ, err t) / (2*Real.pi) ≤ ε := by sorry

end BroughanRH
