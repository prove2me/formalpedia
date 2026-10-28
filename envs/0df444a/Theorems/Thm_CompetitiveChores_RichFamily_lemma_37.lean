-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_37
-- name    : CompetitiveChores.RichFamily.lemma_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:37.867582+00:00
-- url     : https://prove2.me/theorems/ac6be0a9-2510-4e29-a9d8-a578655e95fb
-- title:
--   Lemma 37 — equilibrium prices p_j = v_{i,j} b_i / u_i(z_i) on consumed chores
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$ and $b\in\mathbb R^n_{<0}$, and let $z$ be an allocation that is competitive at prices $p$. Then for every agent $i$ and chore $j$:
--   $$p_j=\frac{v_{i,j}\,b_i}{u_i(z_i)}\quad\text{if } z_{i,j}>0,\qquad p_j\ge\frac{v_{i,j}\,b_i}{u_i(z_i)}\quad\text{if } z_{i,j}=0.$$
--
--   Thus competitive prices are determined by the allocation and the budgets, and a corollary is that the utility profile of a competitive allocation is strictly negative. These formulas are the basis of the price-free characterizations of Lemma 38 and of the utility formula of Lemma 26.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 50, Appendix A.1, Lemma 37

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 37, p. 50: at a competitive allocation `z` with prices `p`,
`p_j = v_{i,j} b_i / u_i(z_i)` if `z_{i,j} > 0` and `p_j ≥ v_{i,j} b_i / u_i(z_i)` if `z_{i,j} = 0`. -/
theorem lemma_37 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (z : Fin n → Fin m → ℝ) (p : Fin m → ℝ)
    (hzp : IsCompetitiveWith v b z p) (i : Fin n) (j : Fin m) :
    (0 < z i j → p j = v i j * b i / utilityProfile v z i) ∧
      (z i j = 0 → v i j * b i / utilityProfile v z i ≤ p j) := by sorry

end CompetitiveChores.RichFamily
