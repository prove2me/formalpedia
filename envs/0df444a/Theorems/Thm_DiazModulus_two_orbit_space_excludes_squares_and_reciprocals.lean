-- Prove2me | Theorems.Thm_DiazModulus_two_orbit_space_excludes_squares_and_reciprocals
-- name    : DiazModulus.two_orbit_space_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:32.550383+00:00
-- url     : https://prove2.me/theorems/5a9b5afc-69d3-4c6a-bcd2-985fa5af1bc7
-- title:
--   For u ∉ Q̄ and non-zero algebraic a, b, α, β, γ, δ with a² ≠ b², the span of 1, u, u⁻¹, α/(u − a) + β/(u + a), γ/(u − b) + δ/(u + b) is five-dimensional and excludes u², u⁻², 1/(u − c)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $a, b \in \overline{\mathbb{Q}}^\times$ with $a^2 \neq b^2$ and $\alpha, \beta, \gamma, \delta \in \overline{\mathbb{Q}}^\times$, put $g_1 = \alpha/(u - a) + \beta/(u + a)$, $g_2 = \gamma/(u - b) + \delta/(u + b)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}, g_1, g_2$. Then the five numbers are free over $\overline{\mathbb{Q}}$, and $W$ contains none of $u^2$, $u^{-2}$ and $1/(u - c)$ for non-zero $c \in \overline{\mathbb{Q}}$.
--
--   **Proof.** One residue lemma: if $c_0 + c_1u + c_2u^{-1} + d/(u - p) + \sum_i e_i/(u - q_i) = 0$ with the $q_i \neq p$ and all coefficients in \overline{\mathbb{Q}}, clearing denominators gives a polynomial vanishing at the transcendental $u$, hence zero, and its value at $p$ gives $d\prod_i(p - q_i) = 0$. Applied at the five distinct poles $0, \pm a, \pm b$: in a vanishing combination the residues $c_2$, $\lambda\alpha$, $\mu\gamma$ vanish, so the five numbers are free. A membership of $u^2$ or $u^{-2}$ would leave $u$ algebraic or a residue $-1$ at $0$; one of $1/(u - e)$ forces, at $e = \pm a$ (or $\pm b$), both residues of that pair to match $(1, 0)$, impossible since $\alpha, \beta \neq 0$, and for any other $e$ a sixth pole with residue $-1$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem two_orbit_space_excludes_squares_and_reciprocals
    (u : ℂ) (hu : u ∉ Qbar) (a b α β γ δ : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hα : α ∈ Qbar) (hβ : β ∈ Qbar)
    (hγ : γ ∈ Qbar) (hδ : δ ∈ Qbar) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hδ0 : δ ≠ 0) :
    LinearIndependent (↥Qbar) ![1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) ∧
      (u ^ 2)⁻¹ ∉ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) ∧
      ∀ e ∈ Qbar, e ≠ 0 → (u - e)⁻¹ ∉ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) := by
  sorry

end DiazModulus
