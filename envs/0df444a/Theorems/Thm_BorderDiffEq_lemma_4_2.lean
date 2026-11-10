-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_2
-- name    : BorderDiffEq.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:08.670267+00:00
-- url     : https://prove2.me/theorems/967a1922-a054-4cd0-9f0d-5bd56552d696
-- title:
--   Lemma 4.2 — Wronskian criterion: $W(f_1,\dots,f_r)=0$ iff the $f_i$ are linearly dependent
-- statement:
--   Let $K$ be a field of characteristic zero and $f_1,\dots,f_r\in K[z]$, with $D=\partial/\partial z$. Then
--   $$
--   W(f_1,\dots,f_r)=0\iff f_1,\dots,f_r \text{ are linearly dependent over } K,
--   $$
--   i.e. iff there are $a_1,\dots,a_r\in K$, not all zero, with $\sum_i a_if_i=0$.
--
--   The paper applies this over $K=F(\varepsilon,y,x)$ to see that the leading coefficient of its differential equation is nonzero (Lemma 5.1).
--
--   **Formalization Note** The $f_i$ form a family indexed by `Fin r`; dependence is `¬ LinearIndependent K f`.
--
--   Differences from the source:
--   - generalization: $F$ of characteristic 0, $f_i\in F(x)[z]$, dependence over $F(x)$ → any field $K$ of characteristic 0, $f_i\in K[z]$, dependence over $K$; reason: $F(x)$ is such a field, so $K=F(x)$ gives the source's statement
--   - generalization: $f_1,\dots,f_r$ non-zero → no non-vanishing hypothesis; reason: if some $f_i=0$ the Wronskian has a zero row and the family is dependent, so both sides hold
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.2, p.24 (Lemma 2.2 of [BS26])

import Mathlib
import Definitions.Def_BorderDiffEq_wronskian

namespace BorderDiffEq

/-- **Lemma 4.2 (Wronskian criterion; Lemma 2.2 of [BS26])** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 4.2, p.24). Let `K` be a field of characteristic zero and
`f₁, …, f_r ∈ K[z]`. Then `W(f₁, …, f_r) = 0` if and only if `f₁, …, f_r` are linearly dependent
over `K`.

**Formalization Note.** The paper states it for `f₁, …, f_r ∈ F(x)[z]` with `F` of characteristic
zero, which is the case `K = F(x)`; the lemma is applied over `F(ε, y, x)` in Lemma 5.1. The
hypothesis "non-zero" is dropped: with some `fᵢ = 0` both sides hold. -/
theorem lemma_4_2 (K : Type) [Field K] [CharZero K] (r : ℕ) (f : Fin r → Polynomial K) :
    wronskian f = 0 ↔ ¬ LinearIndependent K f := by sorry

end BorderDiffEq
