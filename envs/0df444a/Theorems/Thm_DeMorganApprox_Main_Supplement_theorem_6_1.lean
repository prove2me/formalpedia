-- Prove2me | Theorems.Thm_DeMorganApprox_Main_Supplement_theorem_6_1
-- name    : DeMorganApprox.Main.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:45:33.006581+00:00
-- url     : https://prove2.me/theorems/8994f532-5218-49f6-a8c4-3c8a5ab09648
-- title:
--   Theorem 6.1 — tightness: some ≤ n-leaf De Morgan formula needs coefficient ℓ1-norm 2^{Ω(√n)} for every 1/3-approximating polynomial
-- statement:
--   A **De Morgan formula** on input variables $x_1,\dots,x_m$ has $\wedge$ and $\vee$ gates and literal leaves $x_i$ or $\neg x_i$; its size is the number of leaf occurrences. For a real polynomial $P$ in $m$ variables, $\|P\|_1$ denotes its coefficient $\ell_1$-norm in the $\{0,1\}$-monomial basis after multilinearization on the Boolean cube (§3.1).
--
--   **Theorem (tightness of the coefficient bound).** There is an absolute constant $c>0$ such that for all sufficiently large $n$ there is a Boolean function $F:\{0,1\}^m\to\{0,1\}$ computed by a De Morgan formula with at most $n$ leaves with the following property: every real polynomial $P$ in the $m$ input variables satisfying
--
--   $$
--   |P(z)-F(z)|\le\tfrac13\quad\text{for every } z\in\{0,1\}^m
--   $$
--
--   also satisfies
--
--   $$
--   \|P\|_1\;\ge\;2^{c\sqrt n}.
--   $$
--
--   No restriction is placed on the degree of $P$, and $P$ need not be multilinear.
--
--   The theorem shows that the coefficient bound $\|P\|_1\le 2^{O(\sqrt n)}$ of Theorem 1.1 (the goal of this mission) cannot be improved beyond the constant in the exponent, even if the degree bound is dropped.
--
--   **Formalization Note** The $\Omega(\sqrt n)$ is one constant $c>0$ chosen before $n$, the formula and $P$; "for all sufficiently large $n$" is "there is $N$ such that for all $n\ge N$". The number of variables $m$ and the formula are existential, as in the theorem. $P$ ranges over all of `MvPolynomial (Fin m) ℝ`; Boolean inputs are evaluated at their $0/1$ real points, and $\|P\|_1$ is `coeffL1 (multilinearize P)`. Since multilinearization only merges coefficients, this is at most the raw coefficient sum `coeffL1 P`, so the statement also gives the lower bound on the raw sum.
--
--   Differences from the source:
--   - encoding: Ω(√n) in the exponent → one constant c > 0 quantified before n, the formula and P, with exponent c·√n; reason: the standard reading of Ω, the same reading the published goal uses for its O(√n).
--   - encoding: Boolean function F computed by a De Morgan formula with at most n leaves → a formula φ : Formula m with φ.leaves ≤ n, F = φ.eval, m existential; reason: the published negation-normal-form encoding of §3.1, which the base mission's definitions fix.
--   - encoding: ‖P‖₁, the coefficient ℓ1-norm in the {0,1}-monomial basis after multilinearization → coeffL1 (multilinearize P); reason: this is the §3.1 definition verbatim; for multilinear P it is coeffL1 P.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Theorem 6.1, PDF p. 29 (printed p. 27), proof PDF pp. 29–30 (printed pp. 27–28); ‖·‖₁ from §3.1, PDF p. 10 (printed p. 8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf

import Mathlib
import Definitions.Def_DeMorganApprox_Main_Basic
import Definitions.Def_DeMorganApprox_Main_Supplement_Multilinearize

namespace DeMorganApprox.Main.Supplement

open DeMorganApprox.Main

/-- Theorem 6.1 (tightness of the coefficient bound), PDF p. 29 (printed p. 27). One absolute
constant `c > 0` for the `Ω(√n)`, chosen before `n`, the formula and `P`; `P` is any real
polynomial (no multilinearity, no degree bound), and `‖P‖₁` is the paper's §3.1 norm: the
coefficient ℓ1-norm of `P` after multilinearization on the Boolean cube. -/
theorem theorem_6_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (m : ℕ) (φ : Formula m), φ.leaves ≤ n ∧
        ∀ P : MvPolynomial (Fin m) ℝ,
          (∀ x : Fin m → Bool, |MvPolynomial.eval (boolPoint x) P - boolVal (φ.eval x)| ≤ 1 / 3) →
            (2 : ℝ) ^ (c * Real.sqrt (n : ℝ)) ≤ coeffL1 (multilinearize P) := by sorry

end DeMorganApprox.Main.Supplement
