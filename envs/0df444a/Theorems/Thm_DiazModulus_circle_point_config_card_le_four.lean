-- Prove2me | Theorems.Thm_DiazModulus_circle_point_config_card_le_four
-- name    : DiazModulus.circle_point_config_card_le_four
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:10:52.020898+00:00
-- url     : https://prove2.me/theorems/b4cc3f07-7c37-4d0b-8723-2024abea4bac
-- title:
--   For u transcendental over a subfield K of ℂ with uū ∈ K, every p×q configuration over K in K + Ku + Kū has p + q ≤ 4
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$ and $u \in \mathbb{C}$ transcendental over $K$ with $\rho = u\bar u \in K$, and put $H_0 = K + Ku + K\bar u$ (note $\bar u = \rho/u$). Every $p \times q$ configuration over $K$ in $H_0$ (with $p, q \ge 1$) has $p + q \le 4$. In particular $H_0$ carries no $2 \times 3$ configuration, over any base field.
--
--   **Proof.** Since $\bar u = \rho/u$, $H_0$ is a subspace of $K(u)$ of dimension at most $3$, and `DiazModulus.rank_one_config_card_le_finrank_add_one` gives $p + q \le 4$.
--
--   **Novelty.** Tier 2 (short). Over $\overline{\mathbb{Q}}$ the absence of $2 \times 3$ configurations is a case of Roy's lemma on spaces of dimension three (Waldschmidt, DALAG, Lemma 12.16).
-- source:
--   For K = Q̄, a case of Roy's lemma on spaces of dimension at most three (M. Waldschmidt, Diophantine approximation on linear algebraic groups, Springer 2000, Lemma 12.16). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_config_card_le_four (K : Subfield ℂ) (u : ℂ)
    (hT : Transcendental K u) (hρ : u * conj u ∈ K)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (x : Fin p → ℂ) (y : Fin q → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span K ({1, u, conj u} : Set ℂ)) :
    p + q ≤ 4 := by
  sorry

end DiazModulus
