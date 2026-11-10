-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_lemma_4_6
-- name    : EllipticRootFinding.Online.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:02:07.526736+00:00
-- url     : https://prove2.me/theorems/fff52df2-0872-4027-9a3f-ed902e477ea0
-- title:
--   Lemma 4.6 — a square root by exponentiation once j is known
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic greater than $3$, and write $\mathrm{odd}(n) = n / 2^{v_2(n)}$. Let $\beta, z \in F^\times$ with $\beta$ a nonsquare, let $\gamma \in \mathbb Z$ satisfy $2\gamma \equiv 1 \pmod{\mathrm{odd}(q-1)}$, and let $j \in \mathbb Z$ be such that the multiplicative order of $z\beta^{-j}$ is odd. Put
--   $$y = (z\beta^{-j})^{\gamma}\,\beta^{\lfloor j/2 \rfloor}.$$
--   If $z$ is a square, then $j$ is even and $y^2 = z$; if $z$ is not a square, then $j$ is odd and $y^2 = z\beta^{-1}$.
--
--   This is the square-root formula used at Line 8 of Algorithm 2 to lift the roots of $f$ to points of $E$ or of its quadratic twist.
--
--   Differences from the source:
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: β, z ∈ F×q, order(·), β^{−j}, ⌊j/2⌋ → β z : Fˣ, orderOf in Fˣ, integer powers (zpow) in Fˣ, ⌊(j : ℚ)/2⌋, odd(q − 1) = (q − 1)/2^{padicValNat 2 (q − 1)}; 'y is a square root of w' as (y : F)^2 = w; reason: Lean conventions for the same objects; no instance changes
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 18, Lemma 4.6

import Mathlib

namespace EllipticRootFinding.Online

/-- Lemma 4.6 (p. 18). `F` is a finite field with `q` elements, of characteristic `> 3`;
`odd(q − 1) = (q − 1) / 2^{val₂(q − 1)}`; orders are taken in `Fˣ`; `⌊j/2⌋` is the floor;
powers are integer powers in `Fˣ`. -/
theorem lemma_4_6 (F : Type) [Field F] [Fintype F] (hchar : 3 < ringChar F)
    (β z : Fˣ) (hβ : ¬ IsSquare (β : F)) (γ : ℤ)
    (hγ : 2 * γ ≡ 1 [ZMOD (((Fintype.card F - 1) / 2 ^ padicValNat 2 (Fintype.card F - 1) : ℕ) : ℤ)])
    (j : ℤ) (hj : Odd (orderOf (z * β ^ (-j)))) :
    (IsSquare (z : F) →
      Even j ∧ (((z * β ^ (-j)) ^ γ * β ^ ⌊(j : ℚ) / 2⌋ : Fˣ) : F) ^ 2 = (z : F)) ∧
    (¬ IsSquare (z : F) →
      Odd j ∧ (((z * β ^ (-j)) ^ γ * β ^ ⌊(j : ℚ) / 2⌋ : Fˣ) : F) ^ 2 = (z : F) * (β : F)⁻¹) := by sorry

end EllipticRootFinding.Online
