-- Prove2me | Theorems.Thm_DiazModulus_degree_two_configuration_normal_form
-- name    : DiazModulus.degree_two_configuration_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:28.556996+00:00
-- url     : https://prove2.me/theorems/76761d3c-b12b-43ab-8ec3-92176be79f05
-- title:
--   Theorem NF: a 2×3 configuration with ratio of degree 2 in a five-dimensional W ⊇ span(1, u, u⁻¹) makes W complete, two-orbit or cyclic
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $x_0, x_1 \in \mathbb{C}$ be linearly independent and $y_0, y_1, y_2 \in \mathbb{C}$ linearly independent, with $x_iy_j \in W$ for all $i, j$ (a $2 \times 3$ configuration in $W$). Let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and suppose $x_1q(u) = x_0p(u)$, so that the ratio $x_1/x_0$ is $p(u)/q(u)$. Then one of the following holds:
--
--   - **(D1)** there are linearly independent $t_0, t_1, t_2 \in \mathbb{C}$ with $t_j \in W$ and $ut_j \in W$ for every $j$;
--   - **(D2a, two-orbit)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), P'(u)S_2(u)/(uQ'(u)))$ for some $P', Q', S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P', Q'$ coprime, $\max(\deg P', \deg Q') = 2$ and $\deg S_1, \deg S_2 \leq 2$;
--   - **(D2b, cyclic)** $W = \mathrm{span}(1, u, u^{-1}, Q'(u)S_1(u)/(uP'(u)), Q'(u)(Q'(u)S_1(u) + P'(u)S_2(u))/(uP'(u)^2))$ for some such $P', Q', S_1, S_2$.
--
--   $W$ is not assumed to consist of rational functions of $u$; in cases (D2a) and (D2b) the conclusion shows that it does.
--
--   **Proof.** Put $h = p(u)/q(u)$. As $x$ is independent, $x_0 \neq 0$; and $q(u) \neq 0$, for otherwise $x_1q(u) = x_0p(u)$ gives $p(u) = 0$ as well, against a Bézout identity $ap + bq = 1$. So $x_1 = hx_0$, and $y' = x_0y$ is an independent triple (multiplication by $x_0 \neq 0$ is injective) with $y'_j \in W$ and $hy'_j = x_1y_j \in W$. `DiazModulus.degree_two_configuration_multiplier_complement` gives $\lambda \in \{0, 1, 2\}$ and $g_1, g_2$ with $W = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$ and $kg_j \in W$ for $k = q(u)/(p(u) - \lambda q(u))$. The pencil $P = q$, $Q = p - \lambda q$ is coprime of maximal degree $2$ by `DiazModulus.coprime_pencil_mobius` (determinant $-1$), and $k = P(u)/Q(u)$. Then `DiazModulus.quadratic_complement_eigen_forms`, applied to $(g_1, g_2)$ with $S = W$, gives the scalar, two-orbit or cyclic shape, and `DiazModulus.quadratic_eigen_forms_canonical` turns it into (D1), (D2a) or (D2b).
--
--   **Novelty.** Not found in the sources read; the statement is Theorem 2 of the project's own research notes, proved there with vector bundles on $\mathbb{P}^1$ (D2a and D2b are its normal forms after a change of coordinate). The step from a configuration spanning four dimensions to a progression is Lemma 4 of Bachoc, Serra and Zémor (2017). No source on scrolls or on vector bundles on $\mathbb{P}^1$ was among those read.
-- source:
--   Not found in the sources read. The statement is Theorem 2 of the Diaz modulus mission's research notes, with the normal forms of its Q1.3 (D2a and D2b after a change of coordinate), proved there with rank-two vector bundles on the projective line; the proof here is elementary. The step from a configuration spanning four dimensions to a progression is C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), Lemma 4. No source on scrolls or on vector bundles on the projective line was among those read. Uses DiazModulus.degree_two_configuration_multiplier_complement, DiazModulus.coprime_pencil_mobius, DiazModulus.quadratic_complement_eigen_forms and DiazModulus.quadratic_eigen_forms_canonical. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_two_configuration_normal_form (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
    (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ)) := by
  sorry

end DiazModulus
