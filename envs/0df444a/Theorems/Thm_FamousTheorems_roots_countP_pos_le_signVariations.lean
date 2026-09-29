-- Prove2me | Theorems.Thm_FamousTheorems_roots_countP_pos_le_signVariations
-- name    : FamousTheorems.roots_countP_pos_le_signVariations
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:30:23.659537+00:00
-- url     : https://prove2.me/theorems/eed0ad99-9777-4d51-ab21-88f6ca6a2a50
-- title:
--   Descartes' rule of signs
-- statement:
--   **Descartes' rule of signs.**
--
--   For a polynomial $p$ over a linearly ordered commutative ring, the number of positive roots of $p$,
--   counted with multiplicity, is at most the number of sign variations in its coefficient sequence — the
--   number of times consecutive nonzero coefficients differ in sign.
--
--   For example $p(x) = x^3 - 3x + 1$ has coefficient signs $+,-,+$ (ignoring the zero), so two variations,
--   and indeed it has exactly two positive roots. The bound is not always attained, but the gap is always
--   even, so a single sign variation forces exactly one positive root.
--
--   Descartes stated the rule in *La Géométrie* (1637) without proof; Gauss supplied the first complete
--   proof in 1828, including the fact that the deficiency is even. It remains the cheapest useful bound on
--   real root counts — no arithmetic on the polynomial is required, only reading the signs — and it
--   underlies Budan–Fourier and Sturm-sequence root isolation.
--
--   **Formalization note.** `p.roots` is the multiset of roots in $R$, so `countP (0 < ·)` counts positive
--   roots with multiplicity. The result is Mathlib's `Polynomial.roots_countP_pos_le_signVariations`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem roots_countP_pos_le_signVariations : ∀ {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : Polynomial R),
    (p.roots.countP fun x => 0 < x) ≤ p.signVariations := by sorry

end FamousTheorems
