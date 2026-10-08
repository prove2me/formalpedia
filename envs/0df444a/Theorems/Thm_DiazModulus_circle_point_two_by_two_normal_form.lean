-- Prove2me | Theorems.Thm_DiazModulus_circle_point_two_by_two_normal_form
-- name    : DiazModulus.circle_point_two_by_two_normal_form
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:12.767719+00:00
-- url     : https://prove2.me/theorems/098df255-2e44-445e-a9ed-7b42a829b29d
-- title:
--   Normal form: for u transcendental over a subfield K of ℂ with uū ∈ K, the 2×2 configurations over K in K + Ku + Kū are exactly x = μ·P(1, u), y = μ⁻¹·Q(1, ū) with P, Q ∈ GL₂(K)
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K$ be a subfield of $\mathbb{C}$ and $u \in \mathbb{C}$ transcendental over $K$ with $\rho = u\bar u \in K$, and put $H_0 = K + Ku + K\bar u$ (note $\bar u = \rho/u$). Then $x_1, x_2$ and $y_1, y_2$ form a $2 \times 2$ configuration over $K$ in $H_0$ if and only if there are $\mu \neq 0$ and invertible $P, Q \in K^{2 \times 2}$ with
--   $$x_i = \mu\,(P_{i1} + P_{i2}u), \qquad y_j = \mu^{-1}(Q_{1j} + Q_{2j}\bar u).$$
--   Equivalently $(x_iy_j) = P\,N\,Q$ with $N = (1, u)^{T}(1, \bar u)$: the configurations form a single $\mathrm{GL}_2(K) \times \mathrm{GL}_2(K)$-orbit, the orbit of the certificate $(1, u) \otimes (1, \bar u)$ behind `DiazModulus.diaz_of_sfe`.
--
--   **Proof.** If $z_i = \nu(M_{i1} + M_{i2}t)$ with $1, t$ independent and $\nu \neq 0$, then $z$ is independent iff $\det M \neq 0$; this gives the converse, where the products expand into $H_0$ using $u\bar u = \rho$. Forward: $uH_0 = K + Ku + Ku^2$, so $ux_iy_j = A_{ij}(u)$ with $\deg A_{ij} \le 2$, and transcendence turns the vanishing minor into $A_{11}A_{22} = A_{12}A_{21}$ in $K[X]$. Extracting the gcd of $A_{11}, A_{21}$ factors $A_{ij} = a_ib_j$. Neither the $a_i$ nor the $b_j$ can both be constant (else $x$ or $y$ would be dependent), and $\deg a_i + \deg b_j \le 2$, so all have degree at most $1$. With $\mu = x_1/a_1(u)$, $x_i = \mu a_i(u)$ and $y_j = \mu^{-1}b_j(u)/u$, which is the claimed form after $1/u = \bar u/\rho$.
--
--   **Novelty.** Not found in the sources read. It describes every $2 \times 2$ configuration in $H_0$, over any base field.
-- source:
--   Not found in the sources read. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_two_by_two_normal_form (K : Subfield ℂ) (u : ℂ)
    (hT : Transcendental K u) (hρ : u * conj u ∈ K) (x y : Fin 2 → ℂ) :
    (LinearIndependent K x ∧ LinearIndependent K y ∧ ∀ i j, x i * y j ∈ Submodule.span K ({1, u, conj u} : Set ℂ)) ↔
      ∃ (μ : ℂ) (P Q : Matrix (Fin 2) (Fin 2) K), μ ≠ 0 ∧ P.det ≠ 0 ∧ Q.det ≠ 0 ∧
        (∀ i, x i = μ * ((P i 0 : ℂ) + (P i 1 : ℂ) * u)) ∧
        (∀ j, y j = μ⁻¹ * ((Q 0 j : ℂ) + (Q 1 j : ℂ) * conj u)) := by
  sorry

end DiazModulus
