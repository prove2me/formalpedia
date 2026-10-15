-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_18
-- name    : CompetitiveChores.RichFamily.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:39.054319+00:00
-- url     : https://prove2.me/theorems/820d3e7b-ea95-415a-8a07-a9d9c481bfa0
-- title:
--   Lemma 18 — faces of the Pareto frontier ↔ MWW graphs, u(z) ∈ f iff G_z ⊆ G_f
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$. For $\tau\in\mathbb R^n_{>0}$ let $f_\tau$ be the face of the Pareto frontier exposed by $\tau$ (the maximizers of $\langle\tau,u\rangle$ over $\mathcal U(v)$) and $G_\tau=G_\tau(v)$ the MWW graph. Then:
--   1. for all $\tau,\tau'\in\mathbb R^n_{>0}$,
--   $$f_\tau=f_{\tau'}\iff G_\tau=G_{\tau'};$$
--   2. for every $\tau\in\mathbb R^n_{>0}$ and every feasible allocation $z$,
--   $$u(z)\in f_\tau\iff G_z\subseteq G_\tau.$$
--
--   Item 1 says that $f_\tau\mapsto G_\tau$ is a well-defined bijection between the faces of the Pareto frontier and the MWW graphs, and item 2 is the defining property of this bijection in the paper: the utility profile of a feasible allocation lies in a face iff its consumption graph is a subgraph of the face's MWW graph.
--
--   **Formalization Note** The paper states "there is a bijection $f\leftrightarrow G_f$ between faces of the Pareto frontier and MWW graphs" with the membership property. Since faces are those exposed by $\tau\in\mathbb R^n_{>0}$ and MWW graphs are those of $\tau\in\mathbb R^n_{>0}$, this is stated concretely for the bijection $f_\tau\leftrightarrow G_\tau$ used in the paper's proof.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 21, §4.1, Lemma 18

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 18, p. 21: the faces of the Pareto frontier (exposed by `τ ∈ ℝ^n_{>0}`) correspond one to one
to the MWW graphs via `f_τ ↦ G_τ(v)`: two weight vectors expose the same face iff they give the same
MWW graph, and the utility profile of a feasible `z` lies in the face exposed by `τ` iff the
consumption graph of `z` is a subgraph of `G_τ(v)`. -/
theorem lemma_18 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) :
    (∀ τ τ' : Fin n → ℝ, (∀ i, 0 < τ i) → (∀ i, 0 < τ' i) →
      (paretoFace v τ = paretoFace v τ' ↔ mwwGraph v τ = mwwGraph v τ')) ∧
    ∀ τ : Fin n → ℝ, (∀ i, 0 < τ i) → ∀ z, IsFeasible z →
      (utilityProfile v z ∈ paretoFace v τ ↔ consumptionGraph z ⊆ mwwGraph v τ) := by sorry

end CompetitiveChores.RichFamily
