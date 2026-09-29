-- Prove2me | Theorems.Thm_ChebotarevDensity_frobeniusCyclePattern_eq_factorDegrees
-- name    : ChebotarevDensity.frobeniusCyclePattern_eq_factorDegrees
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T17:14:59.7471+00:00
-- url     : https://prove2.me/theorems/2a831596-27a1-4226-ab23-d15af6f4ecef
-- title:
--   Galois theory of finite fields: Frobenius cycle pattern = decomposition type
-- statement:
--   Let $p$ be a prime and let $g\in\mathbb F_p[X]$ be squarefree. Let $L$ be a splitting field of $g$ over $\mathbb F_p$, and let $\mathrm{Frob}:L\to L$, $x\mapsto x^p$, be the Frobenius automorphism, which permutes the zeros of $g$ in $L$. Then the cycle pattern of $\mathrm{Frob}$ on these zeros (cycles of length $1$ included) is the decomposition type of $g$:
--   $$\text{cycle lengths of Frob on }\{g=0\}\;=\;\{\deg h : h \text{ a monic irreducible factor of } g\}\quad\text{(as multisets).}$$
--
--   Applied to $g=f\bmod p$, this is what links Frobenius substitutions to factorizations of $f$ modulo $p$.
--
--   **Formalization Note** Degrees of the normalized (monic) irreducible factors are taken with multiplicity; for squarefree $g$ all multiplicities are $1$.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, p. 33: "Galois theory for finite fields comes down to the statement that the cycle pattern of Frob, viewed as a permutation of the zeros of g, is the same as the decomposition type of g over F_p. This is true for any polynomial g with coefficients in F_p that has no repeated factors."

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem frobeniusCyclePattern_eq_factorDegrees (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X])
    (hg : Squarefree g) :
    frobeniusCyclePattern p g =
      (UniqueFactorizationMonoid.normalizedFactors g).map natDegree := by sorry

end ChebotarevDensity
