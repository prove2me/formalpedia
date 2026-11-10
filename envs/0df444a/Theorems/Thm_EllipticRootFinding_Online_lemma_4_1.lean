-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_lemma_4_1
-- name    : EllipticRootFinding.Online.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:02:05.151169+00:00
-- url     : https://prove2.me/theorems/c1c15ade-3fa4-40aa-bd7e-c32a7b7b5564
-- title:
--   Lemma 4.1 — square roots of h modulo a split separable f
-- statement:
--   Let $F$ be a finite field of characteristic greater than $3$, $f \in F[X]$ split and separable, and $h \in F[X]$.
--
--   1. If $h(\alpha)$ is a square in $F$ for every root $\alpha$ of $f$, then there is $v \in F[X]$ with $\deg v < \deg f$ and $$v^2 \equiv h \pmod f.$$
--   2. If $\beta \in F$ is a nonsquare and $h(\alpha)$ is a nonsquare for every root $\alpha$ of $f$, then there is $v \in F[X]$ with $\deg v < \deg f$ and $\beta v^2 \equiv h \pmod f$.
--
--   The lemma says when the roots of $f$ can be lifted to points of the curve $Y^2 = h(X)$ (item 1) or of its quadratic twist (item 2), which is the existence half of Algorithm 2.
--
--   **Formalization Note.** Degrees are `Polynomial.degree`, so $v = 0$ when $f$ is a nonzero constant.
--
--   Differences from the source:
--   - generalization: h is the right-hand side of the Weierstrass equation Y² = h(X) of §4 → h is an arbitrary polynomial in F[X]; reason: the statement and its interpolation proof never use the shape of h; taking h = X³ + aX + b gives the source's lemma
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: degree less than deg(f); v(X)² ≡ h(X) mod f(X) → v.degree < f.degree (Polynomial.degree, degree 0 = ⊥); f ∣ v² − h and f ∣ C β · v² − h; reason: same meaning
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 14, Lemma 4.1

import Mathlib

open Polynomial

namespace EllipticRootFinding.Online

/-- Lemma 4.1 (p. 14), for a split separable `f` over a finite field `F` of characteristic `> 3`
and an arbitrary polynomial `h`. "Degree less than `deg f`" uses `Polynomial.degree`
(`degree 0 = ⊥`), so `v = 0` when `f` is constant. -/
theorem lemma_4_1 (F : Type) [Field F] [Fintype F] (hchar : 3 < ringChar F)
    (f h : F[X]) (hsplit : f.Splits) (hsep : f.Separable) :
    ((∀ α : F, f.IsRoot α → IsSquare (h.eval α)) →
      ∃ v : F[X], v.degree < f.degree ∧ f ∣ v ^ 2 - h) ∧
    (∀ β : F, ¬ IsSquare β →
      (∀ α : F, f.IsRoot α → ¬ IsSquare (h.eval α)) →
      ∃ v : F[X], v.degree < f.degree ∧ f ∣ C β * v ^ 2 - h) := by sorry

end EllipticRootFinding.Online
