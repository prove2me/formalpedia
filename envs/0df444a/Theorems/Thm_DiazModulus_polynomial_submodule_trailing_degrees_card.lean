-- Prove2me | Theorems.Thm_DiazModulus_polynomial_submodule_trailing_degrees_card
-- name    : DiazModulus.polynomial_submodule_trailing_degrees_card
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:00.054272+00:00
-- url     : https://prove2.me/theorems/f604634b-5bd4-409c-ae3b-680a1e0bf0d4
-- title:
--   For a finite-dimensional K-subspace X of K[X], the trailing degrees of the non-zero elements of X number exactly dim X
-- statement:
--   Let $K$ be a field and $X \subseteq K[X]$ a finite-dimensional $K$-subspace. Then the set $\{\operatorname{ord}_0 f : f \in X,\ f \neq 0\}$ of trailing degrees (orders of vanishing at $0$) has exactly $\dim_K X$ elements.
--
--   This is the valuation count behind linear Cauchy–Davenport (`DiazModulus.polynomial_submodule_mul_finrank_ge`) and the Laurent-hull criterion (`DiazModulus.laurent_hull_config_iff`).
--
--   **Proof.** Induction on $\dim X$. If $X \neq 0$, let $n_0$ be the least trailing degree, attained by $f_0$, and $X' = \{f \in X : f \text{ has coefficient } 0 \text{ at } X^{n_0}\}$. Then $X = X' \oplus Kf_0$, so $\dim X' = \dim X - 1$; an element of $X$ with trailing degree $n > n_0$ lies in $X'$, and no element of $X'$ has trailing degree $n_0$. So the trailing degrees of $X$ are those of $X'$ together with $n_0$.
--
--   **Novelty.** Standard (a valuation with residue field $K$ takes exactly $\dim X$ values on $X \setminus 0$); not claimed. It is the argument Bachoc, Serra and Zémor use in their Theorem 33.
-- source:
--   Standard; the valuation argument as in C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), arXiv:1501.00602, proof of Th. 33. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem polynomial_submodule_trailing_degrees_card (K : Type*) [Field K]
    (X : Submodule K (Polynomial K)) [FiniteDimensional K X] :
    (Polynomial.natTrailingDegree '' ((X : Set (Polynomial K)) \ {0})).ncard =
      Module.finrank K X := by
  sorry

end DiazModulus
