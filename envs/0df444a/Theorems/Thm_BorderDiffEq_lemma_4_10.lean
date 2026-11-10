-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_10
-- name    : BorderDiffEq.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:00.822828+00:00
-- url     : https://prove2.me/theorems/eadc92da-3b25-41d9-8b58-244a0e64e1ef
-- title:
--   Lemma 4.10 — polynomials in the border of $\Sigma^{[s]}\wedge\Sigma$ have ABPs of size $\mathrm{poly}(n,d,s)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $K$ be a field of characteristic zero and $f\in K[x_1,\dots,x_n]$ a polynomial of degree at most $d$ with
--   $$
--   f\in\overline{\Sigma^{[s]}\wedge\Sigma},
--   $$
--   the border of sums of at most $s$ powers of affine forms (exponents unrestricted). Then $f$ is computed by an ABP over $K$ of size at most
--   $$
--   (n+d+s+1)^C .
--   $$
--   The proof of Theorem 2.1 applies this over $F(y)$ to the coefficients $b_j$ of Proposition 5.4 and to the low $z$-coefficients of $f(y+zx)$.
--
--   **Formalization Note** The border has constants in $K((\varepsilon))$ and the condition $f+\varepsilon S$ with $S\in K[[\varepsilon]][x]$; the exponent bound is `⊤` (none). The ABP has affine labels over $K$, and its size is its number of vertices.
--
--   Differences from the source:
--   - reading: $\mathrm{poly}(n,d,s)$ → $(n+d+s+1)^C$ with one absolute $C$ before the field and all parameters; reason: the standard reading of a polynomial bound
--   - generalization: degree $d$ → total degree at most $d$; reason: contains degree exactly $d$
--   - generalization: border with constants in $K(\varepsilon)$ and $g\in K[\varepsilon][x]$ → constants in $K((\varepsilon))$ and $S\in K[[\varepsilon]][x]$; reason: contains the source's approximations
--   - encoding: the paper's field $F$ → any field $K$ of characteristic zero; reason: the paper's $F$ is an arbitrary field of characteristic zero (p.23), and the lemma is applied over $F(y)$
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.10, p.27 (Lemma 52 of [DL25])

import Mathlib
import Definitions.Def_BorderDiffEq_InBorderSWS
import Definitions.Def_BorderDiffEq_ABP

namespace BorderDiffEq

/-- **Lemma 4.10 (Lemma 52 of [DL25]: border sums of powers have small ABPs)**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), Lemma 4.10, p.27). If `f` is an
`n`-variate degree-`d` polynomial in the border `cl(Σ^{[s]}∧Σ)`, then `f` can be computed by an ABP
of size `poly(n, d, s)`.

**Formalization Note.** `poly(n, d, s)` is read as `(n + d + s + 1)^C` with one absolute constant
`C` quantified before the field and every parameter. Any field `K` of characteristic zero (the
proof of Theorem 2.1 applies the lemma over `F(y)`). The border class has top fan-in at most `s`
and no exponent bound (`⊤`), constants in `K((ε))`, and `f + ε·S` with `S ∈ K[[ε]][x]`. "Degree
`d`" is read as "total degree at most `d`". The ABP is over `K` with affine labels; its size is its
number of vertices. -/
theorem lemma_4_10 : ∃ C : ℕ, ∀ (K : Type) [Field K] [CharZero K] (n d s : ℕ)
    (f : MvPolynomial (Fin n) K), f.totalDegree ≤ d → InBorderSWS K (Fin n) s ⊤ f →
    ∃ A : ABP K (Fin n), A.eval = f ∧ A.size ≤ (n + d + s + 1) ^ C := by sorry

end BorderDiffEq
