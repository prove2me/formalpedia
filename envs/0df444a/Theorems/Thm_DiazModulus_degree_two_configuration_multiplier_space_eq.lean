-- Prove2me | Theorems.Thm_DiazModulus_degree_two_configuration_multiplier_space_eq
-- name    : DiazModulus.degree_two_configuration_multiplier_space_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T11:54:50.362179+00:00
-- url     : https://prove2.me/theorems/aa3a8cfe-98e6-4cfa-a672-a4a36d8ff7fc
-- title:
--   In Theorem NF's setting, the f ∈ W with h f ∈ W, h = p(u)/q(u) the ratio of the configuration, form exactly x₀·span(y), of dimension 3
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $x_0, x_1 \in \mathbb{C}$ be linearly independent and $y_0, y_1, y_2 \in \mathbb{C}$ linearly independent, with $x_iy_j \in W$ for all $i, j$ (a $2 \times 3$ configuration in $W$). Let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and suppose $x_1q(u) = x_0p(u)$, so that the ratio $x_1/x_0$ is $h = p(u)/q(u)$. Then:
--
--   - for every $f \in \mathbb{C}$, $f \in W$ and $hf \in W$ if and only if $f \in \mathrm{span}(x_0y_0, x_0y_1, x_0y_2)$;
--   - $W \cap h^{-1}W = \{f \in W : hf \in W\}$ has dimension $3$.
--
--   This is the setting of Theorem NF (`DiazModulus.degree_two_configuration_normal_form`), and the conclusion is the uniqueness of the configuration with ratio $h$: the span of the products $x_0y_j$ is $W \cap h^{-1}W$, which depends only on $W$ and $h$.
--
--   **Proof.** Coprimality and degree give $q \neq 0$, so $q(u) \neq 0$ and $h = p(u)/q(u) = x_1/x_0$. Write $Z = \{f \in W : hf \in W\}$, $y'_j = x_0y_j$, $J = p'q - pq'$ and $g_\lambda(\alpha, \beta) = q(u)(\alpha q(u) + \beta J(u))/(u(p(u) - \lambda q(u)))$. The family $y'$ is independent ($x_0 \neq 0$), $y'_j \in W$ and $hy'_j = x_1y_j \in W$, so $\mathrm{span}(y') \subseteq Z$. **Step 1** (as in `DiazModulus.degree_two_configuration_multiplier_complement`, 10.134): some $\lambda \in \{0, 1, 2\}$ admits no $(\alpha, \beta) \neq (0, 0)$ with $g_\lambda(\alpha, \beta) \in W$, since otherwise `DiazModulus.quadratic_ratio_pole_fractions_independent` would put six independent vectors in the five-dimensional $W$. Put $E = p(u) - \lambda q(u) \neq 0$, $k_0 = q(u)/E$ and $N' = \{g \in W : k_0g \in W\}$. **Step 2:** if $f \in H_0$ and $k_0f \in W$, write $uf = c + au + bu^2 = a'q(u) + b'p(u) + c'J(u)$ by `DiazModulus.quadratic_pencil_wronskian_span`; then $k_0f - b'q(u)/u = g_\lambda(a' + \lambda b', c') \in W$, so $a' + \lambda b' = c' = 0$ and $f = b'E/u$. So $N' \cap H_0 \subseteq \overline{\mathbb{Q}} E/u$, and as $\dim(N' + H_0) \leq 5$ and $\dim H_0 = 3$, $\dim N' \leq 5 + 1 - 3 = 3$. **Step 3:** $V = (E/q(u))\mathrm{span}(y') = (h - \lambda)\mathrm{span}(y')$ has dimension $3$ and lies in $N'$ (for $g \in Z$, $(h - \lambda)g = hg - \lambda g \in W$ and $k_0(h - \lambda)g = g \in W$), so $V = N'$. For $f \in Z$, $(h - \lambda)f \in N' = V$, and cancelling $h - \lambda \neq 0$ gives $f \in \mathrm{span}(y')$. So $Z = \mathrm{span}(y')$, of dimension $3$.
--
--   **Novelty.** Not found in the sources read; routine. It adds what the formal statement of Theorem NF (`DiazModulus.degree_two_configuration_normal_form`, 10.138) leaves out: the span of the products $x_0y_j$ depends only on $W$ and $h$. The proof is that of `DiazModulus.degree_two_configuration_multiplier_complement` (10.134), run on all of $W \cap k_0^{-1}W$.
-- source:
--   Not found in the sources read. It adds what the formal statement of Theorem NF (DiazModulus.degree_two_configuration_normal_form, 10.138) leaves out: the span of the products depends only on W and h. The proof re-runs Steps 1–3 of the sheaf-free proof of Theorem NF (DiazModulus.degree_two_configuration_multiplier_complement, 10.134) on all of W ∩ k₀⁻¹W. Uses DiazModulus.quadratic_pencil_wronskian_span and DiazModulus.quadratic_ratio_pole_fractions_independent. R21a of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_two_configuration_multiplier_space_eq (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    (∀ f : ℂ, (f ∈ W ∧ aeval u p / aeval u q * f ∈ W) ↔
      f ∈ Submodule.span Qbar (Set.range fun j => x 0 * y j)) ∧
    Module.finrank (↥Qbar) ↥(W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) (aeval u p / aeval u q))) = 3 := by
  sorry

end DiazModulus
