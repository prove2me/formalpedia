-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_26
-- name    : CompetitiveChores.RichFamily.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:46.715855+00:00
-- url     : https://prove2.me/theorems/6e1a7f8c-2989-4582-a9c6-2d2cfc158a4f
-- title:
--   Lemma 26 — the utility profile of a competitive allocation with consumption graph G is given by formula (4)
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$ and $b\in\mathbb R^n_{<0}$, and let $G$ be a bipartite graph on $([n],[m])$ with no isolated nodes (every agent and every chore has a neighbour). Let $z$ be a competitive allocation with consumption graph $G_z=G$, and $u=u(z)$. Fix an agent $i$, let $N_i$ be the set of agents of the connected component of $i$ in $G$, and for each $i'\in N_i$ choose any path $\mathcal P_{i,i'}=(i=i_1,j_1,i_2,\dots,i_{L+1}=i')$ of $G$ from $i$ to $i'$. Then
--   $$u_i=\left(\frac{b_i}{\sum_{i'\in N_i}b_{i'}}\right)\cdot\sum_{i'\in N_i}\pi(\mathcal P_{i,i'})\,\bar u_{i'},\tag{4}$$
--   where $\bar z$ divides each chore equally among the agents linked to it in $G$ and $\bar u=u(\bar z)$.
--
--   A competitive utility profile is thus determined by the consumption graph alone, which makes the map from competitive profiles to graphs injective and is the second ingredient of the counting bound of Corollary 25.
--
--   **Formalization Note** The formula is asserted for every choice of the paths $\mathcal P_{i,i'}$, not for a canonical one. For $i'=i$ the trivial path of length $0$ may be chosen, with $\pi(\mathcal P_{i,i})=1$ (the convention of p. 29). The paper writes the component as $N^i$ and $N_i$ interchangeably.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 29, §5, (3) and Lemma 26, formula (4)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 26, p. 29: let `G` be a bipartite graph with no isolated nodes and `z` a competitive allocation
with consumption graph `G`. For an agent `i` and any choice of paths `P_{i,i'}` of `G` from `i` to each
`i'` in the component `N_i` of `i`, formula (4) holds:
`u_i(z_i) = (b_i / ∑_{i' ∈ N_i} b_{i'}) · ∑_{i' ∈ N_i} π(P_{i,i'}) ū_{i'}`, where `ū = u(z̄)` and `z̄` is the
equal split of the chores along `G` (3). -/
theorem lemma_26 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (G : Finset (Fin n × Fin m))
    (hG : (∀ i, ∃ j, (i, j) ∈ G) ∧ ∀ j, ∃ i, (i, j) ∈ G)
    (z : Fin n → Fin m → ℝ) (hz : IsCompetitive v b z) (hzG : consumptionGraph z = G)
    (i : Fin n) (P : Fin n → BPath n m)
    (hP : ∀ i' ∈ component G i, (P i').InGraph G ∧ (P i').agent 0 = i ∧
      (P i').agent (Fin.last (P i').L) = i') :
    utilityProfile v z i =
      (b i / ∑ i' ∈ component G i, b i') *
        ∑ i' ∈ component G i, pathProd v (P i') * utilityProfile v (equalSplit G) i' := by sorry

end CompetitiveChores.RichFamily
