-- Prove2me | Theorems.Thm_ChatterjeeQFT_massShellMeasure_integral
-- name    : ChatterjeeQFT.massShellMeasure_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:29:55.90617+00:00
-- url     : https://prove2.me/theorems/a1e9543a-adfb-4a28-8ac0-e81c87ee19f8
-- title:
--   Integration formula (10.1) for the invariant measure $\lambda_m$
-- statement:
--   This is equation (10.1) of the source. For $m > 0$ and any function $f$ on
--   $\mathbb{R}^{1,3}$ that is almost everywhere strongly measurable for $\lambda_m$,
--
--   $$\int_{X_m} d\lambda_m(p)\, f(p) \;=\; \int_{\mathbb{R}^3} \frac{d^3 q}{(2\pi)^3\, 2\omega_q}\, f(\omega_q, q),$$
--
--   with $\omega_q = \sqrt{m^2 + |q|^2}$. The right-hand side is an ordinary Lebesgue integral over
--   three-momentum space; the formula is what makes $\lambda_m$ usable in computations, and it is the
--   form in which the invariant measure is used throughout the rest of the lectures.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 10 §10.2, p. 42, equation (10.1).

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem massShellMeasure_integral (m : ℝ) (hm : 0 < m) (f : (Fin 4 → ℝ) → ℂ)
    (hf : AEStronglyMeasurable f (massShellMeasure m)) :
    ∫ p, f p ∂(massShellMeasure m)
      = ∫ q : Fin 3 → ℝ, (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))) • f (massShellEmb m q) := by
  sorry

end ChatterjeeQFT
