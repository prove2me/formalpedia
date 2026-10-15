-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_19
-- name    : CompetitiveChores.RichFamily.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:48.166429+00:00
-- url     : https://prove2.me/theorems/32bbd353-9875-4a4c-bafd-1c5cfa6baabb
-- title:
--   Lemma 19 — the set of all MWW graphs is rich
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$. The set of all MWW graphs $\{G_\tau(v):\tau\in\mathbb R^n_{>0}\}$ is rich: for every Pareto optimal utility profile $u\in\mathcal U^*(v)\cap\mathbb R^n_{<0}$ there is a feasible allocation $z$ with $u(z)=u$ whose consumption graph $G_z$ is an MWW graph.
--
--   Lemma 14 alone only gives a consumption graph that is a *subgraph* of an MWW graph; richness means the representative allocation can be chosen so that its consumption graph is itself an MWW graph.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 21, §4.1, Lemma 19

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 19, p. 21: the set of all MWW graphs is rich. -/
theorem lemma_19 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) :
    IsRich v (mwwGraphs v) := by sorry

end CompetitiveChores.RichFamily
