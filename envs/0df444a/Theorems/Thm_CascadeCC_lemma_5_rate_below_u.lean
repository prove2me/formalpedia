-- Prove2me | Theorems.Thm_CascadeCC_lemma_5_rate_below_u
-- name    : CascadeCC.lemma_5_rate_below_u
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:49.373823+00:00
-- url     : https://prove2.me/theorems/4dbc2073-28f0-4928-9150-8de200122cf1
-- title:
--   Lemma 5 — $a^D_j<u$ (corrected: $\lambda>0$)
-- statement:
--   Suppose that $\lambda>0$ and $y_j>0$ for all $j$. Let $T\ge1$ and let $a$ be a stationary optimal solution of DET for $(T,y)$. Then
--
--   $$
--   a_j<u\qquad\text{for all }j.
--   $$
--
--   So the stationary solution never uses the lowest price. This is what puts $a^D$ strictly inside the rate interval in the analysis of the Cascade Correction policy.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - correction: y_j > 0 for all j implies a^D_j < u, with λ ∈ [0, 1] allowed on p.9 → the same under 0 < λ; reason: at λ = 0 the objective is 0 and every a is a stationary optimal solution, including a_j = u with y_j > 0
--   - encoding: a horizon T, a positive integer → 0 < T; reason: at T = 0 stationary optimality is empty
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Lemma 5, p.21

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Lemma 5, p.21 (SSRN abstract_id=3362921), corrected: if y_j > 0 for all j and λ > 0, then a^D_j < u for
all j.

**Formalization Note** λ > 0 is added: at λ = 0 the objective is 0 and every a is stationary optimal,
including a_j = u. It holds for every stationary optimal a. -/
theorem lemma_5_rate_below_u (M : Instance J) (hlam : 0 < M.lam) (T : ℕ) (hT : 0 < T)
    (y : Fin J → ℝ) (hy : ∀ j, 0 < y j) (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) :
    ∀ j, a j < M.u := by sorry

end CascadeCC
