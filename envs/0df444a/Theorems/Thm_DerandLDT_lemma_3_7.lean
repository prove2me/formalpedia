-- Prove2me | Theorems.Thm_DerandLDT_lemma_3_7
-- name    : DerandLDT.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:04:52.239242+00:00
-- url     : https://prove2.me/theorems/1822b63a-81f1-4288-9de5-bbef9c101fb4
-- title:
--   Lemma 3.7 — properties of Hasse derivatives
-- statement:
--   Let $\mathbb F$ be a field of characteristic $p$ and write $\partial$ for the first-order Hasse derivative on $\mathbb F[X]$ (Definition 3.6: $\partial f$ is the coefficient of $Z$ in $f(X + Z)$, which is the formal derivative). Then:
--
--   1. if $f \in \mathbb F[X]$ is nonzero of degree at least one, then $\partial f = 0$ if and only if $f(X) = g(X^p)$ for some $g \in \mathbb F[X]$;
--   2. for all $f, g \in \mathbb F[X]$, $\partial(fg) = g\,\partial f + f\,\partial g$;
--   3. for every $f \in \mathbb F[X]$ and $n \in \mathbb N$, $\partial(f^n) = n f^{n-1} \partial f$.
--
--   These facts control when a restriction of a polynomial to a line is a $p$-th power (Lemma 3.9) and when the $Z$-derivative of the interpolating polynomial is nonzero.
--
--   **Formalization Note** $\partial$ is `Polynomial.hasseDeriv 1` and $g(X^p)$ is `Polynomial.expand F p g`; the characteristic is given by `CharP F p`.
--
--   Differences from the source:
--   - encoding: a field of characteristic p → CharP F p for any natural number p (p = 0 is characteristic zero); reason: in characteristic zero both sides of item 1 are false for deg f ≥ 1, so the item holds there as well
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 3.7, pp.11–12

import Mathlib

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Lemma 3.7** (properties of Hasse derivatives). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 3.7, pp.11–12: *Let `F` be a
field of characteristic `p`. (1) If `f ∈ F[X]` is nonzero of degree at least one, its first order
Hasse derivative is identically zero iff `f(X) = g(X^p)` for some `g ∈ F[X]`. (2) For any two
polynomials, `∂_X(fg) = g·∂_X(f) + f·∂_X(g)`; by induction, `∂_X(fⁿ) = n fⁿ⁻¹ ∂_X(f)` for every
`n ∈ ℕ`.*

**Formalization Note.** `∂_X` is the first Hasse derivative `hasseDeriv 1` (Definition 3.6, p.11),
which equals the formal derivative. `g(X^p)` is `expand F p g`. The characteristic is any `p` with
`CharP F p`; in characteristic `0` both sides of (1) are false for `deg f ≥ 1`. For `n = 0` the
power rule reads `0 = 0`. -/
theorem lemma_3_7 (F : Type u) [Field F] (p : ℕ) [CharP F p] :
    (∀ f : F[X], f ≠ 0 → 1 ≤ f.natDegree →
      (hasseDeriv 1 f = 0 ↔ ∃ g : F[X], expand F p g = f)) ∧
    (∀ f g : F[X], hasseDeriv 1 (f * g) = g * hasseDeriv 1 f + f * hasseDeriv 1 g) ∧
    (∀ (f : F[X]) (n : ℕ), hasseDeriv 1 (f ^ n) = (n : F[X]) * f ^ (n - 1) * hasseDeriv 1 f) := by sorry

end DerandLDT
