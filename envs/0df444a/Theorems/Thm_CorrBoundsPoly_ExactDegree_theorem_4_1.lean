-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_theorem_4_1
-- name    : CorrBoundsPoly.ExactDegree.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:00:24.966695+00:00
-- url     : https://prove2.me/theorems/7d11de6a-e6a8-4fc4-9b29-094a3582c52a
-- title:
--   Theorem 4.1 — explicit cores of every exact degree $d+1$ with $e^{-\pi^2n/(4(d+1)^2)}\le\rho_d(H_{n,d})\le e^{-(\ln3/18)n/(d+1)^2}$, polynomial-time
-- statement:
--   Let $F_s$ ($s\ge1$) be the explicit recursive cores on $M(s)$ variables ($F_1=x_1$; $F_s=\sigma_{s,3s^2}$ for dyadic $s\ge2$; $F_s=\bigoplus_{j=1}^3E_a(X^{(j)})F_t(Y^{(j)})$ on fresh variables otherwise, $s=a+t$, $a$ the largest power of two below $s$), and for $d\ge1$, $n\ge M(d+1)$ let $H_{n,d}$ be the sum of $\lfloor n/M(d+1)\rfloor$ disjoint copies of $F_{d+1}$ on $n$ variables, the remaining variables unused. Then:
--   1. For every $s\ge1$, $F_s$ is a homogeneous Boolean polynomial of degree exactly $s$ on $M(s)\le9s^2$ variables, and
--   $$\rho_{s-1}(F_s)=\nu(F_s)\le\frac13 .$$
--   2. For every $s\ge1$ and $b\ge1$,
--   $$\rho_{s-1}\Big(\bigoplus_{j=1}^bF_s(x^{(j)})\Big)=\nu(F_s)^b\le3^{-b}. \tag{4.1}$$
--   3. For every $d\ge1$ and $n\ge M(d+1)$, $H_{n,d}$ has algebraic degree exactly $d+1$ and
--   $$\exp\Big(-\frac{\pi^2n}{4(d+1)^2}\Big)\le\rho_d(H_{n,d})\le\exp\Big(-\frac{\ln3}{18}\cdot\frac{n}{(d+1)^2}\Big). \tag{4.2}$$
--   4. In particular $n\ge9(d+1)^2$ suffices for $n\ge M(d+1)$.
--   5. All the cores are evaluable in polynomial time: $(s,x)\mapsto F_s(x)$ and $(d,x)\mapsto H_{|x|,d}(x)$ are computable by Turing machines in time polynomial in the input length, with $s$ and $d$ written in unary.
--
--   Here $\rho_d$ is the maximum correlation with **all** Boolean functions of degree at most $d$ on the whole input, cross-block monomials included, and $\nu$ is the normalized rank defect in the truncated algebra. Degree $d+1$ is the least possible degree for a function with small correlation against degree-$d$ tests, and the correlation scale $\exp[-\Theta(n/d^2)]$ is the same as for XOR of majority, whose degree over $\mathbb F_2$ is $\Theta(d^2)$.
--
--   **Formalization Note** $F_s$ is `F s` on `Fin (M s)`; the XOR (4.1) is `xorPow b (evalFn (F s))` on `Fin b × Fin (M s)`; `H n d` places copy `j` on variables `j·M(d+1), …, (j+1)·M(d+1) − 1` of `Fin n`. Polynomial time is `Turing.TM2ComputableInPolyTime` for `evalF`, `evalH : ℕ × List Bool → Bool` (output `false` off the domain) with input encoding `inputEncoding` (unary number, then the bits) and output `Computability.encodingBoolBool`.
--
--   Differences from the source:
--   - encoding: "there is an explicit homogeneous Boolean polynomial $F_s$" → the statement is about the paper's construction `F s` (Eq. (4.6)), with $M(s)$ its actual number of variables; reason: "explicit" refers to this construction
--   - encoding: degree exactly $s$ (resp. $d+1$) → `IsDegExactly` of the Boolean function, plus `IsHomogeneous s` for `F s`; reason: the paper's degree is the multilinear degree (p. 1)
--   - encoding: the blocks $x^{(j)}$ and the copies in $H_{n,d}$ → variable sets `Fin b × Fin (M s)` and the contiguous layout in `Fin n`, unused variables last; reason: relabelling
--   - encoding: "$s=d+1\ge2$" → `1 ≤ d`; $3^{-b}$ → `((3 : ℝ) ^ b)⁻¹`; $\ln$, $\exp$, $\pi$ → `Real.log`, `Real.exp`, `Real.pi`; reason: notation
--   - encoding: "$n\ge9(d+1)^2$ suffices" → `9 * (d + 1) ^ 2 ≤ n → M (d + 1) ≤ n` for `d ≥ 1`; reason: what "suffices" refers to (the hypothesis $n\ge M(s)$)
--   - reading: "all the cores are evaluable in polynomial time" → uniform Turing-machine polynomial time (`Turing.TM2ComputableInPolyTime`) for $(s,x)\mapsto F_s(x)$ and $(d,x)\mapsto H_{|x|,d}(x)$, $s$, $d$ in unary, `false` off the domain; reason: the standard meaning of polynomial-time evaluability of a family; unary parameters make the input length $s+M(s)$ (resp. $d+n$), the natural instance size
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), pp. 30–31 (PDF 32–33), Theorem 4.1, Eqs. (4.1), (4.2); intro version Theorem 1.2, p. 4 (PDF 6); proof p. 32 (PDF 34)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_Cores
import Definitions.Def_CorrBoundsPoly_ExactDegree_PolyTime

namespace CorrBoundsPoly.ExactDegree

/-- **Theorem 4.1** (Exact degree and matching correlation scale; Xin Li, *More on Correlation
Bounds for Polynomials*, pp. 30–31, PDF 32–33). For the explicit recursive cores `F_s` on `M(s)`
variables:
(1) for every `s ≥ 1`, `F_s` is homogeneous of degree exactly `s`, `M(s) ≤ 9s²`, and
`ρ_{s−1}(F_s) = ν(F_s) ≤ 1/3`;
(2) for every `s ≥ 1` and `b ≥ 1`, `ρ_{s−1}(⨁_{j=1}^b F_s(x^{(j)})) = ν(F_s)^b ≤ 3^{−b}` (Eq. (4.1));
(3) for every `d ≥ 1` and `n ≥ M(d+1)`, `H_{n,d}` (`⌊n/M(d+1)⌋` disjoint copies of `F_{d+1}` on `n`
variables, the rest unused) has algebraic degree exactly `d + 1` and
`exp(−π²n/(4(d+1)²)) ≤ ρ_d(H_{n,d}) ≤ exp(−(ln 3/18)·n/(d+1)²)` (Eq. (4.2));
(4) `n ≥ 9(d+1)²` suffices for `n ≥ M(d+1)`;
(5) the cores are evaluable in polynomial time: `(s, x) ↦ F_s(x)` and `(d, x) ↦ H_{|x|,d}(x)` are
computed by Turing machines in time polynomial in the input length (`s`, `d` in unary). -/
theorem theorem_4_1 :
    (∀ s : ℕ, 1 ≤ s →
      (F s).IsHomogeneous s ∧ IsDegExactly (evalFn (F s)) s ∧ M s ≤ 9 * s ^ 2 ∧
      rho (s - 1) (evalFn (F s)) = nu (F s) ∧ nu (F s) ≤ 1 / 3) ∧
    (∀ s : ℕ, 1 ≤ s → ∀ b : ℕ, 1 ≤ b →
      rho (s - 1) (xorPow b (evalFn (F s))) = nu (F s) ^ b ∧
      nu (F s) ^ b ≤ ((3 : ℝ) ^ b)⁻¹) ∧
    (∀ d n : ℕ, 1 ≤ d → M (d + 1) ≤ n →
      IsDegExactly (evalFn (H n d)) (d + 1) ∧
      Real.exp (-(Real.pi ^ 2 * n) / (4 * ((d : ℝ) + 1) ^ 2)) ≤ rho d (evalFn (H n d)) ∧
      rho d (evalFn (H n d)) ≤ Real.exp (-(Real.log 3 / 18) * ((n : ℝ) / ((d : ℝ) + 1) ^ 2))) ∧
    (∀ d n : ℕ, 1 ≤ d → 9 * (d + 1) ^ 2 ≤ n → M (d + 1) ≤ n) ∧
    Nonempty (Turing.TM2ComputableInPolyTime inputEncoding.encode
      Computability.encodingBoolBool.encode evalF) ∧
    Nonempty (Turing.TM2ComputableInPolyTime inputEncoding.encode
      Computability.encodingBoolBool.encode evalH) := by sorry

end CorrBoundsPoly.ExactDegree
