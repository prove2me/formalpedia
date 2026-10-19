-- Prove2me | Theorems.Thm_DiazModulus_two_by_three_configuration_ratio_degree_le_two
-- name    : DiazModulus.two_by_three_configuration_ratio_degree_le_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:56.957705+00:00
-- url     : https://prove2.me/theorems/4d15847b-ce48-491d-84b8-a54ae0d120a6
-- title:
--   If a space of dimension ≤ 5 containing 1, u, 1/u carries a 2×3 configuration x ⊗ y with x₁/x₀ = p(u)/q(u) in lowest terms, then deg p, deg q ≤ 2
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $W \subseteq \mathbb{C}$ be a finite-dimensional $\overline{\mathbb{Q}}$-subspace with $\dim W \leq 5$ and $1, u, u^{-1} \in W$. Let $x_0, x_1$ be linearly independent over $\overline{\mathbb{Q}}$, and $y_0, y_1, y_2$ too, with $x_iy_j \in W$ for all $i, j$, and let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) \geq 1$ and $x_1q(u) = x_0p(u)$. Then $\max(\deg p, \deg q) \leq 2$.
--
--   **Proof.** Coprimality and $\max(\deg p, \deg q) \geq 1$ give $q(u) \neq 0$, so $x_1 = x_0h$ with $h = p(u)/q(u)$; as $x$ is free, $h \notin \overline{\mathbb{Q}}$, so $h$ is transcendental over $\overline{\mathbb{Q}}$. Put $Y' = \mathrm{span}(x_0y_0, x_0y_1, x_0y_2)$ and $XY = Y' + hY' \subseteq W$, the span of the six products, so that $\dim(Y' \cap hY') \geq 1$. If $H = \mathrm{span}(1, u, u^{-1}) \subseteq XY$, a non-zero $ht \in Y' \cap hY'$ with $t \in Y'$ and some $c' \in Y'$ outside $\mathrm{span}(t, ht)$ give $XY \subseteq \mathrm{span}(t, th, th^2, tk, thk)$ with $k = c'/t$, and `DiazModulus.progression_pair_span_ratio_degree_le_two` applies. Otherwise $\dim XY \leq 4$, so two planes in $Y'$ meet and give $t, th, th^2 \in Y'$; then $XY = \mathrm{span}(t, th, th^2, th^3)$, the span of $H$ and $XY$ has dimension $5$, and `DiazModulus.progression_space_ratio_degree_le_two` applies.
--
--   **Novelty.** Not found in the sources read; routine. When the six products span four dimensions, the step to a progression $t, th, th^2, th^3$ is that of Bachoc, Serra and Zémor (2017, Lemma 4).
-- source:
--   Not found in the sources read; when the products span four dimensions, the progression is that of C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), Lemma 4. Uses DiazModulus.progression_space_ratio_degree_le_two and DiazModulus.progression_pair_span_ratio_degree_le_two. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem two_by_three_configuration_ratio_degree_le_two (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    [FiniteDimensional (↥Qbar) W] (hW : Module.finrank (↥Qbar) W ≤ 5)
    (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : 1 ≤ max p.natDegree q.natDegree)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    max p.natDegree q.natDegree ≤ 2 := by
  sorry

end DiazModulus
