-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_theorem_3_1
-- name    : BurkholderDFI.SquareFnLp.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:55:53.877959+00:00
-- url     : https://prove2.me/theorems/e1c81ac9-1684-475c-a738-4c550e2642cc
-- title:
--   Theorem 3.1 — weak type (1,1) of the square function: λP(S(f) > λ) ≤ 3‖f‖₁
-- statement:
--   Let $f = (f_1, f_2, \dots)$ be a martingale or a nonnegative submartingale relative to $\mathcal A_1 \subseteq \mathcal A_2 \subseteq \cdots$, with square function $S(f) = \bigl(\sum_{k\ge1} d_k^2\bigr)^{1/2}$ and $\|f\|_1 = \sup_{n\ge1} E|f_n|$. Then
--   $$\lambda\, P(S(f) > \lambda) \le 3\|f\|_1, \qquad \lambda > 0. \tag{3.1}$$
--
--   The square function is thus of weak type $(1,1)$ with constant $3$; this is one of the main results of Burkholder's 1966 paper, here obtained from Lemma 2.1.
--
--   **Formalization Note** No $L^1$-boundedness is assumed: when $\|f\|_1 = \infty$ the right side is $+\infty$ in $[0,\infty]$ and the inequality is trivial, as in the paper's "we may assume that $f$ is $L^1$-bounded". $S(f)$ takes values in $[0, \infty]$. The Mathlib convention at index $0$ is as in (1.1).
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 3.1, p. 21, display (3.1)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem theorem_3_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal l * P {ω | ENNReal.ofReal l < sqFn f ω} ≤ 3 * pNorm P 1 f := by sorry

end BurkholderDFI.SquareFnLp
