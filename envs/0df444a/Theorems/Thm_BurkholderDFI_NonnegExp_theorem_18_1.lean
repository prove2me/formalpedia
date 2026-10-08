-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegExp_theorem_18_1
-- name    : BurkholderDFI.NonnegExp.theorem_18_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:22.930889+00:00
-- url     : https://prove2.me/theorems/02ed563b-049b-424c-9744-fb1e0a7c11a5
-- title:
--   Theorem 18.1 — exponential square integrability before exit
-- statement:
--   Let $f=(f_n)_{n\ge1}$ be a nonnegative martingale on a probability space, let $\lambda>0$, and set $\mu=\inf\{n\ge1:|f_n|>\lambda\}$. Then $S_{\mu-1}(f)$ is finite almost everywhere and, for every $0<t<1/(3\lambda^2)$,
--
--   $$
--   E\exp\bigl(tS_{\mu-1}(f)^2\bigr)
--     \le\frac{1}{1-3t\lambda^2}.
--   $$
--
--   The result strengthens the second-moment estimate for the stopped square function to exponential square integrability.
--
--   **Formalization Note** The paper states $S_{\mu-1}(f)\in\exp L^2$ before the display; almost-everywhere finiteness is included explicitly so that converting an extended value to a real one cannot hide infinity. Nonnegativity is almost everywhere for $n\ge1$; Mathlib's index $0$ is auxiliary. The stopped square function is $S(f)$ on $\{\mu=\infty\}$, and the expectation is an extended nonnegative integral.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 18.1 and (18.2), p. 35; https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem 18.1, p. 35: exponential square integrability of the stopped square function. -/
theorem theorem_18_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) (l : ℝ) (hl : 0 < l) :
    (∀ᵐ ω ∂P, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 / (3 * l ^ 2) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - 3 * t * l ^ 2)) := by sorry

end BurkholderDFI.NonnegExp
