-- Prove2me | Theorems.Thm_DiazModulus_rank_one_config_card_le_finrank_add_one
-- name    : DiazModulus.rank_one_config_card_le_finrank_add_one
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:45.719259+00:00
-- url     : https://prove2.me/theorems/13e9574b-ef87-4cc0-8354-7049fc6d19c6
-- title:
--   For u transcendental over a subfield K of ℂ and a finite-dimensional K-space V₀ ⊆ K(u), every p×q configuration over K in V₀ has p + q ≤ dim V₀ + 1
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$, $u$ transcendental over $K$, and $V_0 \subseteq K(u)$ a finite-dimensional $K$-subspace. Every $p \times q$ configuration over $K$ in $V_0$ with $p, q \ge 1$ has $p + q \le \dim_K V_0 + 1$.
--
--   For $V_0 = K + Ku + K\bar u$ with $u\bar u \in K$ (dimension $3$) it gives $p + q \le 4$, so no $2 \times 3$ configuration.
--
--   **Proof.** Clear denominators: there is $g$ with $g(u) \neq 0$ and polynomials $A_{ij}$ with $A_{ij}(u) = g(u)x_iy_j$. Evaluation at $u$ is injective, so $A_{i1}A_{1j} = A_{11}A_{ij}$ in $K[X]$. Then $P = \operatorname{span}\{A_{i1}\}$ and $Q = \operatorname{span}\{A_{1j}\}$ have dimensions $p$ and $q$, $PQ \subseteq A_{11}\cdot\operatorname{span}\{A_{ij}\}$, and $v \mapsto v(u)/g(u)$ embeds $\operatorname{span}\{A_{ij}\}$ into $V_0$. Linear Cauchy–Davenport (`DiazModulus.polynomial_submodule_mul_finrank_ge`) gives $p + q \le \dim PQ + 1 \le \dim V_0 + 1$.
--
--   **Novelty.** Not found in the sources read in this form; it is short: linear Cauchy–Davenport (`DiazModulus.polynomial_submodule_mul_finrank_ge`) after clearing denominators.
-- source:
--   Linear Cauchy–Davenport (S. Eliahou, C. Lecouvey, Th. 6.2, as stated in C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), arXiv:1501.00602, Th. 2) applied to configurations in K(u). R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rank_one_config_card_le_finrank_add_one (K : Subfield ℂ) (u : ℂ)
    (hT : Transcendental K u) (V₀ : Submodule K ℂ) [FiniteDimensional K V₀]
    (hV₀ : ∀ v ∈ V₀, v ∈ IntermediateField.adjoin K ({u} : Set ℂ))
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (x : Fin p → ℂ) (y : Fin q → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀) :
    p + q ≤ Module.finrank K V₀ + 1 := by
  sorry

end DiazModulus
