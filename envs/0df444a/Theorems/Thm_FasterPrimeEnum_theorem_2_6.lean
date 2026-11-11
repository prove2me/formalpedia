-- Prove2me | Theorems.Thm_FasterPrimeEnum_theorem_2_6
-- name    : FasterPrimeEnum.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:35.384234+00:00
-- url     : https://prove2.me/theorems/6efc69f9-6b7d-4075-ab5f-ef03b214d323
-- title:
--   Theorem 2.6 — $H_d$ counts the representations $m^2p^l$ modulo 2
-- statement:
--   Let $D=\{-1,-2,2\}$ and $\chi_d(n)=\left(\frac dn\right)$. For each $d\in D$,
--
--   $$
--   H_d(x)\equiv\sum_{\substack{m\ge1\\ m\text{ odd}}}\ \sum_{\substack{p\ge3\\ \chi_d(p)=1}}\ \sum_{l\ge1}x^{m^2p^l}\pmod 2,
--   $$
--
--   and consequently
--
--   $$
--   (H_{-1}+H_{-2}+H_2)(x)\equiv\sum_{\substack{m\ge1\\ m\text{ odd}}}\ \sum_{\substack{p\ge3\\ l\ge1}}x^{m^2p^l}\pmod 2,
--   $$
--
--   where $p$ always runs over primes. A monomial may occur several times on the right; for instance $27=1^2\cdot3^3=3^2\cdot3$.
--
--   The second congruence is the generating function the core algorithm evaluates: modulo $2$, and up to the sparse terms with $l\ge2$, it is the indicator of the odd square-primes.
--
--   **Formalization Note** Both congruences are stated coefficientwise: the coefficient of $x^n$ on the right is the number of triples $(m,p,l)$ with $m$ odd, $p\ge3$ prime (with $\chi_d(p)=1$ in the first), $l\ge1$ and $m^2p^l=n$; all such triples lie in $[0,n]^3$.
--
--   Differences from the source:
--   - encoding: congruences of formal power series modulo 2 → for every n, the coefficient of x^n on the left is congruent modulo 2, in ℤ, to the number of triples (m, p, l) ∈ [0, n]³ with m²p^l = n and the stated conditions; reason: two series are congruent modulo 2 exactly when all coefficients are; every triple with m²p^l = n has m, p, l ≤ n
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 2.6, eqs. (2.6)–(2.7), p.15

import Mathlib
import Definitions.Def_FasterPrimeEnum_restrictedProd
import Definitions.Def_FasterPrimeEnum_H

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **Theorem 2.6** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.15.

"For each d ∈ D, (2.6) H_d(x) ≡ Σ_{m⩾1, m odd} Σ_{p⩾3, χ_d(p)=1} Σ_{l⩾1} x^{m²p^l} (mod 2).
Consequently (2.7) (H_{−1} + H_{−2} + H_2)(x) ≡ Σ_{m⩾1, m odd} Σ_{p⩾3, l⩾1} x^{m²p^l} (mod 2).
Note that summation over the variable p always indicates a sum over primes."

**Formalization Note.** Stated coefficientwise: the coefficient of `x^n` on the right is the number
of triples `(m, p, l)` with `m` odd, `p ⩾ 3` prime (with `χ_d(p) = jacobiSym d p = 1` in (2.6)),
`l ⩾ 1` and `m²p^l = n`, counted with multiplicity (Remark 2.7). Every such triple has
`m, p, l ⩽ n`, so the count over `[0, n]³` is the full count. Both (2.6) and (2.7) are stated. -/
theorem theorem_2_6 :
    (∀ d ∈ D, ∀ n : ℕ,
      H d n ≡ (((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        fun t : ℕ × ℕ × ℕ => t.1 % 2 = 1 ∧ t.2.1.Prime ∧ 3 ≤ t.2.1 ∧
          jacobiSym d t.2.1 = 1 ∧ 1 ≤ t.2.2 ∧ t.1 ^ 2 * t.2.1 ^ t.2.2 = n).card : ℤ) [ZMOD 2]) ∧
    (∀ n : ℕ,
      H (-1) n + H (-2) n + H 2 n ≡
        (((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          fun t : ℕ × ℕ × ℕ => t.1 % 2 = 1 ∧ t.2.1.Prime ∧ 3 ≤ t.2.1 ∧
            1 ≤ t.2.2 ∧ t.1 ^ 2 * t.2.1 ^ t.2.2 = n).card : ℤ) [ZMOD 2]) := by sorry

end FasterPrimeEnum
