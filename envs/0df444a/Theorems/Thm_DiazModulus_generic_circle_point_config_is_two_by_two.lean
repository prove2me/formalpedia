-- Prove2me | Theorems.Thm_DiazModulus_generic_circle_point_config_is_two_by_two
-- name    : DiazModulus.generic_circle_point_config_is_two_by_two
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:26.33698+00:00
-- url     : https://prove2.me/theorems/4c3f8499-e9a2-4f38-b083-0ea578528eb4
-- title:
--   For u, w₁…w_m algebraically independent over a subfield K of ℂ with uū ∈ K, every p×q configuration over K (p, q ≥ 2) in K + Ku + Kū + Kw₁ + … + Kw_m is 2×2 and lies in K + Ku + Kū
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$, let $u, w_1, \dots, w_m$ be algebraically independent over $K$, suppose $\rho = u\bar u \in K$, and put $H_0 = K + Ku + K\bar u$. Every $p \times q$ configuration over $K$ with $p, q \ge 2$ in $H_0 + Kw_1 + \dots + Kw_m$ has $p = q = 2$ and all its products in $H_0$.
--
--   For $K = \overline{\mathbb{Q}}$ this contains `DiazModulus.generic_circle_point_no_two_by_three_configuration`.
--
--   **Proof.** The algebraic independence of $u, w_1, \dots, w_m$ over $K$ makes $u$ transcendental over $K$ and $w_1, \dots, w_m$ algebraically independent over $K(u)$. Since $H_0 \subseteq K(u)$, `DiazModulus.rank_one_config_separation` puts every product in $H_0$, and `DiazModulus.circle_point_config_card_le_four` gives $p + q \le 4$, so $p = q = 2$.
--
--   **Novelty.** Not found in the sources read; it is short: separation (`DiazModulus.rank_one_config_separation`) plus `DiazModulus.circle_point_config_card_le_four`. It extends the library's $\overline{\mathbb{Q}}$ statement to any base field.
-- source:
--   Not found in the sources read; extends DiazModulus.generic_circle_point_no_two_by_three_configuration to any base field. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_circle_point_config_is_two_by_two (K : Subfield ℂ) (u : ℂ)
    (hρ : u * conj u ∈ K) (m : ℕ) (w : Fin m → ℂ)
    (hgen : AlgebraicIndependent K (Fin.cons u w : Fin (m + 1) → ℂ))
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (x : Fin p → ℂ) (y : Fin q → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span K (({1, u, conj u} : Set ℂ) ∪ Set.range w)) :
    p = 2 ∧ q = 2 ∧ ∀ i j, x i * y j ∈ Submodule.span K ({1, u, conj u} : Set ℂ) := by
  sorry

end DiazModulus
