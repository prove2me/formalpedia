-- Prove2me | Theorems.Thm_DiazModulus_polynomial_submodule_degrees_card
-- name    : DiazModulus.polynomial_submodule_degrees_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:59:02.807191+00:00
-- url     : https://prove2.me/theorems/f20af94c-8f92-4d07-8838-cab4283833a0
-- title:
--   A finite-dimensional K-subspace of K[X] has exactly as many distinct degrees as its dimension
-- statement:
--   Let $K$ be a field and $X \subseteq K[X]$ a finite-dimensional $K$-subspace. Then the set of degrees of the non-zero elements of $X$ has exactly $\dim X$ elements.
--
--   **Proof.** $X$ is spanned by finitely many polynomials, so its degrees are bounded. Induction on $\dim X$: let $n_0$ be the largest degree, attained by $f_0 \in X$, and $X' = X \cap \ker(f \mapsto f_{n_0})$. Then $X = X' \oplus Kf_0$ (the coefficient of $f_0$ at $n_0$ is its leading one), an element of $X$ of degree below $n_0$ lies in $X'$, and no element of $X'$ has degree $n_0$. So the degrees of $X$ are those of $X'$ and $n_0$.
--
--   **Novelty.** The degree form of `DiazModulus.polynomial_submodule_trailing_degrees_card`; the valuation count of Bachoc, Serra and Zémor (2017, §7, proof of Th. 33). Routine.
-- source:
--   Not found in the sources read in this form; the degree form of DiazModulus.polynomial_submodule_trailing_degrees_card. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem polynomial_submodule_degrees_card (K : Type*) [Field K]
    (X : Submodule K (Polynomial K)) [FiniteDimensional K X] :
    (Polynomial.natDegree '' ((X : Set (Polynomial K)) \ {0})).ncard =
      Module.finrank K X := by
  sorry

end DiazModulus
