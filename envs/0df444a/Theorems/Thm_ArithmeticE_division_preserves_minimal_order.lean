-- Prove2me | Theorems.Thm_ArithmeticE_division_preserves_minimal_order
-- name    : ArithmeticE.division_preserves_minimal_order
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T20:54:26.406126+00:00
-- url     : https://prove2.me/theorems/6e7d145b-73da-498c-872d-7808c339ba00
-- title:
--   Division by one minus X preserves minimal differential order
-- statement:
--   Let $g\in\mathbb C[[X]]$ and let $L=\sum_{k=0}^n p_kD^k$ be a minimal polynomial differential equation for $(1-X)g$. Then $g$ has a minimal equation $M$ of the same order $n$, with leading coefficient $(1-X)p_n$.
--
--   The forward operator is $M=L\circ(1-X)$, whose coefficients are $(1-X)p_k-(k+1)p_{k+1}$, with the last correction omitted at $k=n$. Minimality follows from the reverse identity
--   $$
--   (1-X)^{k+1}D^kg=\sum_{j=0}^k\frac{k!}{j!}(1-X)^jD^j((1-X)g).
--   $$
--   Multiplying an order-$k$ equation for $g$ by $(1-X)^{k+1}$ therefore produces an order-$k$ polynomial equation for $(1-X)g$, with nonzero leading coefficient. A smaller equation would contradict minimality of $L$.
--
--   This proves the rational gauge step used in the classical zero-singularity argument. No arithmetic regularity or zero-singularity theorem is assumed or proved by this statement.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, proof of Corollary 2.2, pp. 3–4: the minimal operator of the quotient is L composed with multiplication by the linear factor. The reverse-jet identity makes the minimality argument explicit.

import Definitions.Def_beukersLiftingData
open ArithmeticE

theorem ArithmeticE.division_preserves_minimal_order (g : PowerSeries ℂ) (p : ℕ → Polynomial ℂ) (n : ℕ)
    (hm : MinimalEquation p n ((1-PowerSeries.X)*g)) :
    ∃ q : ℕ → Polynomial ℂ, MinimalEquation q n g ∧ q n = (1-Polynomial.X)*p n := by sorry
