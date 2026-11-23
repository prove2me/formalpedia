-- Prove2me | Theorems.Thm_BroughanRH_bagchiHardyInterval
-- name    : BroughanRH.bagchiHardyInterval
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:30.952822+00:00
-- url     : https://prove2.me/theorems/26ca2f9c-67aa-43e5-93c6-39258974a986
-- title:
--   Bagchi’s Hardy-space approximation with a real parameter
-- statement:
--   In the Hardy space on $\operatorname{Re}s>1/2$, the closed linear span of $F_p(s)=(p^s-p)\zeta(s)/s$ for $0\leq p\leq1$ contains $s\mapsto1/s$. The formula uses the removable value at $s=1$. [Source](https://arxiv.org/abs/math/0607733).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §3.4 (Bagchi, Thm. 2(iii)). https://arxiv.org/abs/math/0607733

import Mathlib

namespace BroughanRH

theorem bagchiHardyInterval :
    let G (p : ℝ) (s : ℂ) : ℂ := if s = 1 then ((p * Real.log p : ℝ) : ℂ)
      else ((p : ℂ)^s - (p : ℂ)) * riemannZeta s / s
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      ∃ p : Fin N → Set.Icc (0 : ℝ) 1,
      ∀ σ : ℝ, 1/2 < σ →
        let err (t : ℝ) := let s := (σ : ℂ) + (t : ℂ)*Complex.I
                           ‖s⁻¹ - ∑ j, a j * G (p j) s‖^2
        MeasureTheory.Integrable err ∧ (∫ t : ℝ, err t) / (2*Real.pi) ≤ ε := by sorry

end BroughanRH
