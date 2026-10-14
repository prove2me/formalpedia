-- Prove2me | Theorems.Thm_DiazModulus_quadratic_over_ratio_of_mem_progression_pair_span
-- name    : DiazModulus.quadratic_over_ratio_of_mem_progression_pair_span
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:26.642532+00:00
-- url     : https://prove2.me/theorems/e75901ad-2b66-468f-9ffb-ad07ba72742b
-- title:
--   For u ∉ Q̄, c ≠ 0 and h ∉ Q̄: if 1, u, u⁻¹ lie in the Q̄-span of c, ch, ch², ck, chk, then u is a root of a non-zero quadratic over Q̄[h]
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $c, h, k \in \mathbb{C}$ with $c \neq 0$, and suppose $1, u, u^{-1}$ lie in the $\overline{\mathbb{Q}}$-span of $c, ch, ch^2, ck, chk$. If $h \notin \overline{\mathbb{Q}}$, there are $A, B, C \in \overline{\mathbb{Q}}[X]$, not all zero, with $A(h)u^2 + B(h)u + C(h) = 0$.
--
--   A configuration $(1, h) \otimes Y$ whose products span a five-dimensional $W \supseteq \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ gives, after normalisation, $W = c\cdot\mathrm{span}(1, h, h^2, k, hk)$ (research notes R12, Q1; not formalised). So no such configuration has a ratio of degree $3$ or more.
--
--   **Proof.** Unpacking the three memberships gives $1 = c(a_0(h) + k\,b_0(h))$, $u = c(a_1(h) + k\,b_1(h))$ and $u^{-1} = c(a_2(h) + k\,b_2(h))$ with $a_i, b_i \in \overline{\mathbb{Q}}[X]$: three vectors in the two-dimensional $\overline{\mathbb{Q}}(h)$-span of $c$ and $ck$. Write $D_{ij} = a_ib_j - a_jb_i$. If $D_{01} \neq 0$, the identity $D_{12}\,w_0 - D_{02}\,w_1 + D_{01}\,w_2 = 0$ for $w_i = a_i(h) + k\,b_i(h)$, together with $uu^{-1} = 1$, gives $(A, B, C) = (-D_{02}, D_{12}, D_{01})$. If $D_{01} = 0$, then $a_0(h)u = a_1(h)$ and $b_0(h)u = b_1(h)$, and $a_0$ or $b_0$ is non-zero (otherwise $1 = 0$), which gives a relation of degree one. Only $u \neq 0$ is used; $h \notin \overline{\mathbb{Q}}$ makes the relation non-trivial as an equation in $u$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem quadratic_over_ratio_of_mem_progression_pair_span
    (u : ℂ) (hu : u ∉ Qbar) (c h k : ℂ) (hc : c ≠ 0) (hh : h ∉ Qbar)
    (h1 : (1 : ℂ) ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) (hu1 : u ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) (hui : u⁻¹ ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) :
    ∃ A B C : Polynomial ↥Qbar, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
      Polynomial.aeval h A * u ^ 2 + Polynomial.aeval h B * u + Polynomial.aeval h C = 0 := by
  sorry

end DiazModulus
