-- Prove2me | Theorems.Thm_DRSubmodHull_lemma_4_8_P_mem_Zset
-- name    : DRSubmodHull.lemma_4_8_P_mem_Zset
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:51.70674+00:00
-- url     : https://prove2.me/theorems/eee3aed8-3e6f-49b8-a193-774a62ae5429
-- title:
--   Lemma 4.8 — the points $P(\mathcal S)$ lie in $\mathcal Z(\mathcal G,u)$
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   For every $\mathcal S\subseteq\mathcal V$, the point $P(\mathcal S)$ of (9) is feasible:
--   $$
--   P(\mathcal S)\in\mathcal Z(\mathcal G,u).
--   $$
--
--   Together with Corollary 4.20 this gives $\mathcal{CZ}\subseteq\mathrm{conv}(\mathcal Z(\mathcal G,u))$.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Lemma 4.8, p.9

import Mathlib
import Definitions.Def_DRSubmodHull_Ppt

set_option autoImplicit false

namespace DRSubmodHull

/-- **Lemma 4.8** (Yu, Küçükyavuz, arXiv:2211.07726v2, §4, p.9). For any `𝒮 ⊆ 𝒱`,
`P(𝒮) ∈ 𝒵(𝒢, u)`.

The hypotheses are the paper's standing conditions (pp.4–5) and, as on p.8 ("In what follows,
all `𝒵(𝒢, u)` satisfy Assumption 1 as well as Property 4.2"), Assumption 1 and Property 4.2. -/
theorem lemma_4_8_P_mem_Zset {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (S : Finset V) :
    Ppt A N u S ∈ Zset A N u := by sorry

end DRSubmodHull
