-- Prove2me | Theorems.Thm_DiazModulus_degree_two_configuration_multiplier_complement
-- name    : DiazModulus.degree_two_configuration_multiplier_complement
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:27.75244+00:00
-- url     : https://prove2.me/theorems/b7f5def8-63f9-4d19-b2c1-1520e8a3748f
-- title:
--   If W ⊇ span(1, u, u⁻¹) has dimension 5 and carries (1, h) ⊗ y with h of degree 2, then W = H₀ ⊕ U with q/(p − λq)·U ⊆ W, λ ∈ {0, 1, 2}
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and let $y_0, y_1, y_2 \in W$ be linearly independent with $(p(u)/q(u))\,y_j \in W$ for every $j$. Then there are $\lambda \in \{0, 1, 2\}$ and $g_1, g_2 \in \mathbb{C}$ such that, with $k = q(u)/(p(u) - \lambda q(u))$, $W = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, $kg_1 \in W$ and $kg_2 \in W$.
--
--   As $\dim W = 5$, this is $W = H_0 \oplus U$ with $U = \overline{\mathbb{Q}} g_1 + \overline{\mathbb{Q}} g_2$ and $kU \subseteq W$.
--
--   **Proof.** Write $J = p'q - pq'$ and $g_\lambda(\alpha, \beta) = q(u)(\alpha q(u) + \beta J(u))/(u(p(u) - \lambda q(u)))$. **Step 1.** If every $\lambda \in \{0, 1, 2\}$ had some $(\alpha, \beta) \neq (0, 0)$ with $g_\lambda(\alpha, \beta) \in W$, then `DiazModulus.quadratic_ratio_pole_fractions_independent` would make $1, u, u^{-1}$ and these three fractions six independent vectors of the five-dimensional $W$. So fix $\lambda$ with no such pair, and put $E = p(u) - \lambda q(u) \neq 0$ and $k = q(u)/E$. **Step 2.** The $Y_j = (E/q(u))y_j = hy_j - \lambda y_j$, with $h = p(u)/q(u)$, lie in $W$, are independent, and $kY_j = y_j \in W$; so $kV \subseteq W$ for $V = \mathrm{span}(Y_0, Y_1, Y_2)$. For $f \in V \cap H_0$, write $f = R(u)/u$ with $\deg R \leq 2$; `DiazModulus.quadratic_pencil_wronskian_span` gives $R = a'q + b'p + c'J$, and then $kf - b'q(u)/u = g_\lambda(a' + \lambda b', c') \in W$, so $a' + \lambda b' = c' = 0$ and $f = b'E/u$: hence $V \cap H_0 \subseteq \overline{\mathbb{Q}} E/u$. **Step 3.** $\dim(V + H_0) = 3 + 3 - \dim(V \cap H_0) \geq 5 = \dim W$, so $V + H_0 = W$ and $V \cap H_0 \neq 0$. A non-zero $f = \sum_jc_jY_j$ in $V \cap H_0$ has some $c_j \neq 0$; the other two $Y_i$ are $g_1, g_2$, and as $Y_j \in \mathrm{span}(f, g_1, g_2)$, $W = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, with $kg_1, kg_2 \in W$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Steps 1–3 of the sheaf-free proof of Theorem NF. Uses DiazModulus.quadratic_pencil_wronskian_span and DiazModulus.quadratic_ratio_pole_fractions_independent. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_two_configuration_multiplier_complement (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (y : Fin 3 → ℂ) (hy : LinearIndependent (↥Qbar) y) (hyW : ∀ j, y j ∈ W)
    (hyh : ∀ j, aeval u p / aeval u q * y j ∈ W) :
    ∃ lam : ↥Qbar, (lam = 0 ∨ lam = 1 ∨ lam = 2) ∧ ∃ g₁ g₂ : ℂ,
      W = Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ) ∧
      aeval u q / (aeval u p - (lam : ℂ) * aeval u q) * g₁ ∈ W ∧
      aeval u q / (aeval u p - (lam : ℂ) * aeval u q) * g₂ ∈ W := by
  sorry

end DiazModulus
