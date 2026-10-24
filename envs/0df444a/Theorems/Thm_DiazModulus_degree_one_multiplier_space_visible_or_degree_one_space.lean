-- Prove2me | Theorems.Thm_DiazModulus_degree_one_multiplier_space_visible_or_degree_one_space
-- name    : DiazModulus.degree_one_multiplier_space_visible_or_degree_one_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:26.270975+00:00
-- url     : https://prove2.me/theorems/a3ae9ca7-9f2c-4dc3-9cce-e72ef3936e06
-- title:
--   A five-dimensional W ⊇ span(1, u, u⁻¹) has three independent t with t, ut ∈ W iff it contains u², u⁻², 1/(u − a), or is H₀ + Q̄g + Q̄ug
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $W \subseteq \mathbb{C}$ be a $\overline{\mathbb{Q}}$-vector subspace of dimension $5$ with $1, u, u^{-1} \in W$, that is, $H_0 \subseteq W$ for $H_0 = \mathrm{span}(1, u, u^{-1})$. Then the following are equivalent:
--
--   - there are linearly independent $t_0, t_1, t_2 \in \mathbb{C}$ with $t_j \in W$ and $ut_j \in W$ for every $j$ (condition (D1));
--   - $u^2 \in W$, or $u^{-2} \in W$, or $(u - a)^{-1} \in W$ for some $a \in \overline{\mathbb{Q}}$ with $a \neq 0$, or there is $g \in \mathbb{C}$ such that $1, u, u^{-1}, g, ug$ are linearly independent and $W = \mathrm{span}(1, u, u^{-1}, g, ug)$.
--
--   The alternatives before the last say that $W$ is visible: it contains $u^2$, $u^{-2}$ or $(u - a)^{-1}$, the elements of Theorem B (when $u\bar u$ is algebraic, $u^{-2}$ is an algebraic multiple of $\bar u^2$). The last is the degree-one space $H_0 + \overline{\mathbb{Q}} g + \overline{\mathbb{Q}} ug$.
--
--   **Proof.** $H_0$ has dimension $3$, $u$ being transcendental. ($\Rightarrow$) If every $t_j$ lies in $H_0$, their span is $H_0$, so $u$ is a combination of the $t_j$ and $u \cdot u = u^2 \in W$. Otherwise take $g = t_j \notin H_0$. If $(u - c)g \in H_0$ for some $c \in \overline{\mathbb{Q}}$, write $(u - c)g = \alpha + \beta u + \gamma u^{-1}$: for $c = 0$, $\gamma \neq 0$ (else $g \in H_0$) and $u^{-2} = \gamma^{-1}(g - \beta - \alpha u^{-1}) \in W$; for $c \neq 0$, with $r = \alpha + \beta c + \gamma/c$ one has $(u - c)(g - \beta + (\gamma/c)u^{-1}) = r$, so $r \neq 0$ (else $g \in H_0$) and $(u - c)^{-1} \in W$. If there is no such $c$, then $1, u, u^{-1}, g, ug$ are independent (a relation with a non-zero coefficient of $ug$ or of $g$ would put some $(u - c)g$ or $g$ in $H_0$), and they span $W$ by dimension. ($\Leftarrow$) Take $t = (1, u, u^{-1})$, $(1, u^{-1}, u^{-2})$, $(1, u^{-1}, (u - a)^{-1})$ (using $u(u - a)^{-1} = 1 + a(u - a)^{-1}$) or $(1, u^{-1}, g)$; independence comes from the transcendence of $u$ (a vanishing polynomial of degree at most $2$) or from that of $1, u, u^{-1}, g, ug$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem degree_one_multiplier_space_visible_or_degree_one_space (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) :
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ↔ (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ (∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) ∨
      ∃ g : ℂ, LinearIndependent (↥Qbar) ![1, u, u⁻¹, g, u * g] ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, g, u * g} : Set ℂ)) := by
  sorry

end DiazModulus
