-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_corollary_21
-- name    : CompetitiveChores.RichFamily.corollary_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:57.413411+00:00
-- url     : https://prove2.me/theorems/cb49b25c-b45b-4073-a4c9-7cf0cdb7d6ad
-- title:
--   Corollary 21 — MWW_non-lonely(v) is rich and corresponds to the faces meeting ℝ^n_<0
-- statement:
--   Let $n\ge1$ and $v\in\mathbb R^{n\times m}_{<0}$. Then
--   1. the family $\mathrm{MWW}_{non\text{-}lonely}(v)$ of MWW graphs with no lonely agents is rich;
--   2. under the bijection $f_\tau\leftrightarrow G_\tau(v)$ of Lemma 18 it corresponds to the faces of the Pareto frontier that meet the negative orthant: for every $\tau\in\mathbb R^n_{>0}$,
--   $$f_\tau\cap\mathbb R^n_{<0}\neq\emptyset\iff G_\tau(v)\text{ has no lonely agents}.$$
--
--   Together with Lemma 18 this identifies the faces counted in Corollary 25 with the graphs in $\mathrm{MWW}_{non\text{-}lonely}(v)$.
--
--   **Formalization Note** $n\ge1$ is added: the paper's set of agents is non-empty. With no agents and at least one chore there is no feasible allocation, every face is empty, and the empty graph trivially has no lonely agents, so item 2 would fail.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 23, §4.1, Corollary 21

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Corollary 21, p. 23: `MWW_{non-lonely}(v)` is rich, and under the correspondence of Lemma 18 it
corresponds to the faces `f` of the Pareto frontier with `f ∩ ℝ^n_{<0} ≠ ∅`. -/
theorem corollary_21 (hn : 0 < n) (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) :
    IsRich v (mwwNonLonely v) ∧
      ∀ τ : Fin n → ℝ, (∀ i, 0 < τ i) →
        ((∃ u ∈ paretoFace v τ, ∀ i, u i < 0) ↔ NoLonelyAgents (mwwGraph v τ)) := by sorry

end CompetitiveChores.RichFamily
