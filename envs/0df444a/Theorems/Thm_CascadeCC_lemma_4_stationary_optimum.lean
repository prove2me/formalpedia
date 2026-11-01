-- Prove2me | Theorems.Thm_CascadeCC_lemma_4_stationary_optimum
-- name    : CascadeCC.lemma_4_stationary_optimum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:46.176629+00:00
-- url     : https://prove2.me/theorems/236bcd82-2d4a-454e-ad52-b38fb2b7d9c6
-- title:
--   Lemma 4 — DET has a stationary optimal solution (corrected: $r_j$ continuous at $0$)
-- statement:
--   Suppose that each $r_j$ is continuous on $[0,u]$. For every horizon $T\ge1$ and inventory $y\ge0$ there are rates $a\in[0,u]^J$ such that the constant schedule $\alpha_{tj}=a_j$ is optimal in DET: $T\sigma_j(a)a_j\le y_j$, and every feasible schedule has objective at most $T\sum_j\sigma_j(a)r_j(a_j)$.
--
--   This gives the reformulation (13) of DET as a one-period problem, and it supplies the rates $a^D$ on which both policies of the paper are built.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - correction: there exists an optimal solution of DET with α_tj = a_j, under A1–A3 → the same under continuity of r_j on [0, u], with r_j(0) = 0; reason: counterexample satisfying A1–A3 with Ω_α = (0, 1]: u = 1, J = 2, λ = ζ_j = T = 1, y large, r₁(α) = (1 − α)(1 + 2α), r₂ = 100 r₁; the objective after optimizing product 2 is (1 − a)(113.5 + 2a), strictly decreasing on (0, 1], with supremum 113.5, and the turn-off a = 0 earns 112.5
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Lemma 4, p.20

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Lemma 4, p.20 (SSRN abstract_id=3362921), corrected: DET has a stationary optimal solution, when r_j
is continuous on [0, u].

**Formalization Note** Continuity at 0 is added, since `r j 0 = 0`: without it the supremum need not be
attained (u = 1, J = 2, λ = ζ_j = T = 1, y large, r₁(α) = (1 − α)(1 + 2α), r₂ = 100 r₁). -/
theorem lemma_4_stationary_optimum (M : Instance J)
    (hr : ∀ j, ContinuousOn (M.r j) (Set.Icc 0 M.u)) (T : ℕ) (hT : 0 < T) (y : Fin J → ℝ)
    (hy : ∀ j, 0 ≤ y j) : ∃ a : Fin J → ℝ, IsStationaryOptimal M T y a := by sorry

end CascadeCC
