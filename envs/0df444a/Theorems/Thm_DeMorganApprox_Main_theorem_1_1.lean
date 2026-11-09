-- Prove2me | Theorems.Thm_DeMorganApprox_Main_theorem_1_1
-- name    : DeMorganApprox.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:12.596764+00:00
-- url     : https://prove2.me/theorems/2faf2cbc-9d7f-42c5-b99c-26592e881c96
-- title:
--   Theorem 1.1 — every n-leaf De Morgan formula has a 1/3-approximating multilinear polynomial of degree O(√n) and ℓ1-norm 2^{O(√n)}
-- statement:
--   Let $F:\{0,1\}^m\to\{0,1\}$ be computed by a De Morgan formula with $n$ leaf occurrences. Then there is a real multilinear polynomial $P$ in the $m$ input variables such that, for every $x\in\{0,1\}^m$,
--   $$|P(x)-F(x)|\le\frac13,$$
--   and
--   $$\deg P=O(\sqrt n),\qquad \|P\|_1\le2^{O(\sqrt n)},$$
--   where $\|P\|_1$ is the sum of the absolute values of the coefficients of $P$ in the $\{0,1\}$-monomial basis. The constant in $O(\cdot)$ is absolute: it depends neither on $m$, nor on $n$, nor on the formula.
--
--   The degree bound recovers the known approximate-degree bound for formulas; the coefficient bound is optimal up to the constant in the exponent (Theorem 6.1) and removes the logarithmic losses of earlier estimates.
--
--   Differences from the source:
--   - encoding: a De Morgan formula over {∧, ∨, ¬} with negations pushed to the leaves, size = number of leaf occurrences → the inductive type Formula m with literal leaves lit i b (b = true for xᵢ, false for ¬xᵢ) and binary and/or gates; leaves counts leaf occurrences; reason: this is the negation-normal form of §3.1; §1.1 notes it is equivalent to allowing NOT gates, and pushing negations does not change the leaf count
--   - encoding: inputs x ∈ {0,1}^m and values F(x) ∈ {0,1} → x : Fin m → Bool, the polynomial evaluated at the 0/1 real point boolPoint x, the value boolVal (F x) ∈ {0,1}; reason: the same Boolean cube and the same real values
--   - reading: deg P = O(√n) and ‖P‖₁ ≤ 2^{O(√n)} → ∃ C > 0, chosen before m and the formula, with totalDegree P ≤ C√n and coeffL1 P ≤ 2^{C√n} (real power); reason: O(·) is one absolute constant; a constant chosen after the formula would make the statement trivial by exact interpolation
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Theorem 1.1 (restated as Theorem 5.1, PDF p. 17, printed p. 15), PDF pp. 5–6 (printed pp. 3–4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF pp. 28–29 (printed pp. 26–27)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_Basic

namespace DeMorganApprox.Main

/-- Theorem 1.1 (= Theorem 5.1), PDF pp. 5–6 and 17 (printed pp. 3–4 and 15). One absolute
constant `C`, chosen before `m` and the formula. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (φ : Formula m),
      ∃ P : MvPolynomial (Fin m) ℝ, IsMultilinear P ∧
        (∀ x : Fin m → Bool, |MvPolynomial.eval (boolPoint x) P - boolVal (φ.eval x)| ≤ 1 / 3) ∧
        (P.totalDegree : ℝ) ≤ C * Real.sqrt (φ.leaves : ℝ) ∧
        coeffL1 P ≤ (2 : ℝ) ^ (C * Real.sqrt (φ.leaves : ℝ)) := by sorry

end DeMorganApprox.Main
