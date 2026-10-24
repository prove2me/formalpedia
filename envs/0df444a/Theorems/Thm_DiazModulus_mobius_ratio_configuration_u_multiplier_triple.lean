-- Prove2me | Theorems.Thm_DiazModulus_mobius_ratio_configuration_u_multiplier_triple
-- name    : DiazModulus.mobius_ratio_configuration_u_multiplier_triple
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:34.889994+00:00
-- url     : https://prove2.me/theorems/8614c70e-7c4d-4220-a29b-9594252822a5
-- title:
--   A 2×3 configuration whose ratio is a Möbius function of u gives three independent y′ with y′ and u·y′ in W
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W$ be any $\overline{\mathbb{Q}}$-subspace of $\mathbb{C}$, let $x_0, x_1 \in \mathbb{C}$ be linearly independent and $y_0, y_1, y_2 \in \mathbb{C}$ linearly independent, with $x_iy_j \in W$ for all $i, j$ (a $2 \times 3$ configuration in $W$), and let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 1$ and $x_1q(u) = x_0p(u)$, so the ratio $x_1/x_0$ is a Möbius function of $u$. Then there are linearly independent $y'_0, y'_1, y'_2 \in \mathbb{C}$ with $y'_j \in W$ and $uy'_j \in W$ for every $j$.
--
--   So $(1, u) \otimes y'$ is a configuration in $W$, with ratio $u$.
--
--   **Proof.** Write $p = aX + b$ and $q = cX + d$. To begin, $q \neq 0$: otherwise $x_0p(u) = 0$, so $p = 0$ ($u$ is transcendental) and $0, 0$ are not coprime; hence $q(u) \neq 0$. Next $D = ad - bc \neq 0$. If $c \neq 0$, $D = 0$ gives $cp(u) = aq(u)$, so $cx_1 = ax_0$, and the independence of $x$ forces $c = 0$. If $c = 0$, then $q(u) = d \neq 0$, so $D = 0$ forces $a = 0$, and neither $p$ nor $q$ has a term in $X$, against $\max(\deg p, \deg q) = 1$. Put $y'_j = x_0y_j/q(u)$, a non-zero multiple of the independent family $y$, so $y'$ is independent. As $x_0y_j = q(u)y'_j$ and $x_1y_j = p(u)y'_j$, inverting the matrix of $(p, q)$ in the basis $(X, 1)$ gives $Dy'_j = a\,x_0y_j - c\,x_1y_j$ and $Duy'_j = d\,x_1y_j - b\,x_0y_j$; both lie in $W$, and so do $y'_j$ and $uy'_j$ after dividing by $D \in \overline{\mathbb{Q}}$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem mobius_ratio_configuration_u_multiplier_triple (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 1)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    ∃ y' : Fin 3 → ℂ, LinearIndependent (↥Qbar) y' ∧ ∀ j, y' j ∈ W ∧ u * y' j ∈ W := by
  sorry

end DiazModulus
