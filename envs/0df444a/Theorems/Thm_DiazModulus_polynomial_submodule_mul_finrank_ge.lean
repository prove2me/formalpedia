-- Prove2me | Theorems.Thm_DiazModulus_polynomial_submodule_mul_finrank_ge
-- name    : DiazModulus.polynomial_submodule_mul_finrank_ge
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:03.345645+00:00
-- url     : https://prove2.me/theorems/493fa5ef-b99c-411b-8f1e-80c5901c9183
-- title:
--   Linear Cauchy–Davenport in K[X]: for non-zero finite-dimensional K-subspaces X, Y of K[X], dim X + dim Y ≤ dim(XY) + 1
-- statement:
--   Let $K$ be a field and $X, Y \subseteq K[X]$ non-zero finite-dimensional $K$-subspaces, and let $XY$ be the $K$-span of the products $fg$, $f \in X$, $g \in Y$. Then $\dim X + \dim Y \le \dim XY + 1$.
--
--   **Proof.** Let $A, B, C$ be the trailing-degree sets of $X$, $Y$ and $XY$; by `DiazModulus.polynomial_submodule_trailing_degrees_card` their sizes are the three dimensions. For non-zero $f \in X$, $g \in Y$, $fg$ is a non-zero element of $XY$ of trailing degree $\operatorname{ord} f + \operatorname{ord} g$, so $A + B \subseteq C$, and $|A + B| \ge |A| + |B| - 1$ in $\mathbb{N}$ (Cauchy–Davenport in a linearly ordered cancellative monoid).
--
--   **Novelty.** Known: it is a case of the linear Cauchy–Davenport theorem (Eliahou–Lecouvey, Th. 6.2; Hou–Leung–Xiang for separable extensions), as stated by Bachoc, Serra and Zémor (2017, Th. 2), since $K$ is algebraically closed in $K(X)$. Not claimed.
-- source:
--   A case of the linear Cauchy–Davenport theorem (S. Eliahou, C. Lecouvey, Th. 6.2), as stated in C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), arXiv:1501.00602, Th. 2. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem polynomial_submodule_mul_finrank_ge (K : Type*) [Field K]
    (X Y : Submodule K (Polynomial K)) [FiniteDimensional K X] [FiniteDimensional K Y]
    (hX : X ≠ ⊥) (hY : Y ≠ ⊥) :
    Module.finrank K X + Module.finrank K Y ≤ Module.finrank K ↥(X * Y) + 1 := by
  sorry

end DiazModulus
