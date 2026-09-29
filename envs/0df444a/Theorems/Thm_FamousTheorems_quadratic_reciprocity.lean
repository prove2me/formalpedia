-- Prove2me | Theorems.Thm_FamousTheorems_quadratic_reciprocity
-- name    : FamousTheorems.quadratic_reciprocity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:12.548922+00:00
-- url     : https://prove2.me/theorems/c40363e3-d77e-44c8-9990-af3e232e2eb1
-- title:
--   The law of quadratic reciprocity
-- statement:
--   **Gauss's law of quadratic reciprocity.**
--
--   For distinct odd primes $p, q$,
--   $$\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\cdot\frac{q-1}{2}} .$$
--
--   So the two questions "is $p$ a square mod $q$?" and "is $q$ a square mod $p$?" have the same
--   answer unless both primes are $3 \bmod 4$, in which case the answers are opposite. There is no
--   a priori reason these should be related at all, which is what makes the law startling.
--
--   Conjectured by Euler and Legendre; Gauss gave the first complete proof in 1796 at eighteen and
--   returned to it repeatedly, eventually publishing eight proofs — he called it the
--   *aureum theorema*, the golden theorem. Over two hundred proofs are now known.
--
--   It is the first case of class field theory: the generalisations to higher powers (Eisenstein,
--   Kummer) and to Artin reciprocity are among the central achievements of algebraic number theory.
--
--   **Formalization note.** The exponent uses natural division, so $p/2 = (p-1)/2$ for odd $p$.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem quadratic_reciprocity : ∀ {p q : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)],
    p ≠ 2 → q ≠ 2 → p ≠ q →
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by sorry

end FamousTheorems
