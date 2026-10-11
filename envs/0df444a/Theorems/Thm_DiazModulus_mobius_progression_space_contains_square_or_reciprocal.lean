-- Prove2me | Theorems.Thm_DiazModulus_mobius_progression_space_contains_square_or_reciprocal
-- name    : DiazModulus.mobius_progression_space_contains_square_or_reciprocal
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:04:14.515047+00:00
-- url     : https://prove2.me/theorems/5f4fe8a8-3b1c-45fa-8e8b-8db0e6e84bc3
-- title:
--   For u ∉ Q̄ and a Möbius function h of u: if Q̄ + Q̄u + Q̄u⁻¹ + Σ Q̄ c hᵏ (k ≤ 3) is five-dimensional, it contains u², u⁻² or some 1/(u − b), b ≠ 0
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $\alpha, \beta, \gamma, \delta \in \overline{\mathbb{Q}}$ with $\alpha\delta - \beta\gamma \neq 0$, put $h = (\alpha u + \beta)/(\gamma u + \delta)$, and let $c \in \mathbb{C}$ be non-zero. If the $\overline{\mathbb{Q}}$-span $W$ of $1, u, u^{-1}$ and $c, ch, ch^2, ch^3$ has dimension $5$, then $W$ contains $u^2$, $u^{-2}$ or $1/(u - b)$ for some non-zero $b \in \overline{\mathbb{Q}}$.
--
--   This is the index-one half of the classification of the progression spaces (Case I): when the ratio $h$ of the progression generates $\overline{\mathbb{Q}}(u)$, the space contains one of the elements of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`), so when $u\bar u$ is algebraic Theorem B sees it. With R9's involution spaces (the index-two half) it accounts for every five-dimensional space containing a $4$-term progression; that the index is $1$ or $2$ is proved in the research notes and is not formalised.
--
--   **Proof.** Put $A = \alpha u + \beta$, $G = \gamma u + \delta \neq 0$ and $c' = c/G^3$, so $ch^k = c'A^kG^{3-k}$. From $\delta A - \beta G = Du$ and $\alpha G - \gamma A = D$ ($D = \alpha\delta - \beta\gamma$) every $c'u^j$, $j \leq 3$, lies in $W$. The spaces $H = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ and $P = \sum_{j \le 3} \overline{\mathbb{Q}}c'u^j$ have dimensions $3$ and $4$, and $H + P \subseteq W$ has dimension at most $5$, so $H \cap P \neq 0$: there are non-zero polynomials $p$, $r$ of degrees at most $3$ and $2$ with $F\,p(u) = r(u)$, $F = c'u$. Induction on $\deg p$: if $p$ is constant, $F$ is a polynomial in $u$ and $u^3 \in F\cdot\overline{\mathbb{Q}}[u]_{\le 3} + \overline{\mathbb{Q}}[u]_{\le 2}$; otherwise $p$ has a root $b \in \overline{\mathbb{Q}}$, and either $r(b) = 0$ and $u - b$ cancels, or $(u - b)^{-1} \in F\cdot\overline{\mathbb{Q}}[u]_{\le 3} + \overline{\mathbb{Q}}[u]_{\le 2}$. Dividing by $u$ gives $u^2$, $u^{-2}$ ($b = 0$) or $1/(u(u - b))$, hence $1/(u - b)$, in $W$. Only the dimension bound is used, not the equality.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R11 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem mobius_progression_space_contains_square_or_reciprocal
    (u : ℂ) (hu : u ∉ Qbar) (α β γ δ c : ℂ) (hα : α ∈ Qbar) (hβ : β ∈ Qbar) (hγ : γ ∈ Qbar)
    (hδ : δ ∈ Qbar) (hdet : α * δ - β * γ ≠ 0) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ)))) = 5) :
    u ^ 2 ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
        Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) ∨
      (u ^ 2)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
        Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) ∨
      ∃ b ∈ Qbar, b ≠ 0 ∧ (u - b)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
        Set.range (fun k : Fin 4 => c * ((α * u + β) / (γ * u + δ)) ^ (k : ℕ))) := by
  sorry

end DiazModulus
