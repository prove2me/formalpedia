-- Prove2me | Theorems.Thm_DiazModulus_rank_one_config_separation_two
-- name    : DiazModulus.rank_one_config_separation_two
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:23.473979+00:00
-- url     : https://prove2.me/theorems/fccd2c36-8b8a-4d53-b05f-e6d7a9c0803f
-- title:
--   For subfields K ≤ F of ℂ, a K-space V₀ ⊆ F and w transcendental over F: a 2×2 configuration over K with all products in V₀ + Kw has all products in V₀
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K \subseteq F$ be subfields of $\mathbb{C}$, $V_0 \subseteq F$ a $K$-subspace, and $w$ transcendental over $F$. If $x_1, x_2$ and $y_1, y_2$ form a $2 \times 2$ configuration over $K$ in $V_0 + Kw$, then every $x_iy_j$ lies in $V_0$: the transcendental number never enters. The coefficients of $w$ must lie in $K$, not in $F$.
--
--   **Proof.** Write $x_iy_j = c_{ij} + \ell_{ij}w$ with $c_{ij} \in V_0 \subseteq F$ and $\ell_{ij} \in K$. Since $(x_1y_1)(x_2y_2) = (x_1y_2)(x_2y_1)$, the polynomial $\det(C + XL)$ over $F$ vanishes at $w$, so its leading coefficient $\det L$ is $0$. If a column $j$ of $L$ were non-zero, $z = \ell_{2j}x_1 - \ell_{1j}x_2$ would be non-zero ($x$ is $K$-independent) with $zy_1, zy_2 \in F$ (because $\det L = 0$). For each row $i$, $(zy_1)(x_iy_2) = (zy_2)(x_iy_1)$ is linear in $w$ over $F$, so $z(\ell_{i2}y_1 - \ell_{i1}y_2) = 0$, and $K$-independence of $y$ makes the whole row of $L$ vanish, a contradiction. So $L = 0$ and $x_iy_j = c_{ij} \in V_0$.
--
--   **Novelty.** Not found in the sources read; it is short. The step that `DiazModulus.rank_one_config_separation` iterates.
-- source:
--   Not found in the sources read (the separation step of the polar-degree note). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rank_one_config_separation_two (K F : Subfield ℂ) (hKF : K ≤ F)
    (V₀ : Submodule K ℂ) (hV₀ : ∀ v ∈ V₀, v ∈ F) (w : ℂ) (hw : Transcendental F w)
    (x y : Fin 2 → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀ ⊔ Submodule.span K {w}) :
    ∀ i j, x i * y j ∈ V₀ := by
  sorry

end DiazModulus
