-- Prove2me | Theorems.Thm_CompetitiveChores_IndivisibleRounding_cycle_elimination
-- name    : CompetitiveChores.IndivisibleRounding.cycle_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:18.020817+00:00
-- url     : https://prove2.me/theorems/106e6987-bc38-4d30-b76f-1f03b3818f10
-- title:
--   §7, pp. 37–38, proof of Theorem 35, first step — an acyclic competitive allocation with the same utilities, prices and budgets
-- statement:
--   Cycle elimination for competitive allocations of chores.
--
--   Let $v\in\mathbb R^{n\times m}_{<0}$ and $b\in\mathbb R^n_{<0}$, and let $z$ be competitive for $(v,b)$ at prices $p$. Then there is a feasible allocation $z^{\mathrm{acyc}}$ with
--
--   $$u(z^{\mathrm{acyc}})=u(z),\qquad G_{z^{\mathrm{acyc}}}\ \text{acyclic},$$
--
--   which is competitive for the same budgets $b$ at the same prices $p$.
--
--   This is the first step of the rounding behind Theorem 35: Algorithm 3 takes as input an acyclic consumption graph of a competitive allocation together with its prices.
--
--   **Formalization Note** The page combines two sentences: the existence of $z^{\mathrm{acyc}}$ with the same utility profile and an acyclic consumption graph, and "By Lemmas 36 and 37, the allocation $z^{\mathrm{acyc}}$ is competitive with the same $p$ and $b$". Both are part of the conclusion. Acyclic means no simple cycle $(i_1,j_1,\dots,j_L,i_1)$ with $L\ge2$ in the consumption graph.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, pp. 37–38, §7, proof of Theorem 35, first step

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Graphs

namespace CompetitiveChores.IndivisibleRounding

/-- §7, pp. 37–38, proof of Theorem 35, first step: a competitive allocation `z` at prices `p` can be
replaced by a feasible allocation `z^acyc` with the same utility profile and an acyclic consumption
graph, which is competitive with the same prices `p` and budgets `b`. -/
theorem cycle_elimination {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i < 0) (z : Fin n → Fin m → ℝ) (p : Fin m → ℝ)
    (hz : CompetitiveChores.RichFamily.IsCompetitiveWith v b z p) :
    ∃ z' : Fin n → Fin m → ℝ, CompetitiveChores.RichFamily.IsFeasible z' ∧ CompetitiveChores.RichFamily.utilityProfile v z' = CompetitiveChores.RichFamily.utilityProfile v z ∧
      IsAcyclic (CompetitiveChores.RichFamily.consumptionGraph z') ∧ CompetitiveChores.RichFamily.IsCompetitiveWith v b z' p := by sorry

end CompetitiveChores.IndivisibleRounding
