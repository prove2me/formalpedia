-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_36
-- name    : CompetitiveChores.RichFamily.lemma_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:26.72103+00:00
-- url     : https://prove2.me/theorems/841435f5-cf69-4026-ab48-015169212818
-- title:
--   Lemma 36 — competitive at prices p ⇔ MBB condition and budget exhaustion
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$ be a matrix of values and $b\in\mathbb R^n_{<0}$ a vector of budgets. Let $z$ be a feasible allocation and $p\in\mathbb R^m_{<0}$ a vector of prices. Then $z$ is competitive at prices $p$ if and only if both of the following hold:
--   1. **MBB condition:** for all agents $i$ and chores $j,c$,
--   $$z_{i,j}>0\ \Longrightarrow\ \frac{v_{i,j}}{|p_j|}\ge\frac{v_{i,c}}{|p_c|};$$
--   2. **budget exhaustion:** $b_i=\sum_{j=1}^m p_jz_{i,j}$ for every agent $i$.
--
--   In words, every agent consumes only chores with the best (least negative) ratio of value to price and spends exactly her budget. This price characterization is the first-order condition of the agents' problems and is used throughout the paper.
--
--   **Formalization Note** The paper writes $p\in\mathbb R^n_{<0}$; prices are indexed by chores, so this is $p\in\mathbb R^m_{<0}$.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 50, Appendix A.1, Lemma 36

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 36, p. 50: for `v`, `b` with strictly negative entries, a feasible allocation `z` is competitive
at the strictly negative prices `p` iff the MBB condition and budget exhaustion hold. -/
theorem lemma_36 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (z : Fin n → Fin m → ℝ) (hz : IsFeasible z) (p : Fin m → ℝ)
    (hp : ∀ j, p j < 0) :
    IsCompetitiveWith v b z p ↔
      ((∀ i j, 0 < z i j → ∀ c, v i c / |p c| ≤ v i j / |p j|) ∧
        ∀ i, b i = bundlePrice p (z i)) := by sorry

end CompetitiveChores.RichFamily
