-- Prove2me | Theorems.Thm_CascadeCC_scaled_value
-- name    : CascadeCC.scaled_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:36.319701+00:00
-- url     : https://prove2.me/theorems/574478ea-6e8f-43f9-af13-d621a1746ea0
-- title:
--   §7.1 and (13) — $V^{k,D}=kV^D=kT\tilde V^D$
-- statement:
--   Let $a$ be a stationary optimal solution of DET for $(T,y)$, $T\ge1$, $y\ge0$. Let $k\ge1$ be such that $N=kT$ and $Y_j=ky_j$ are natural numbers. Then $a$ is a stationary optimal solution for $(N,Y)$, and with $\tilde V^D=\sum_j\sigma_j(a)r_j(a_j)$,
--
--   $$
--   V^{k,D}=N\tilde V^D,\qquad V^D=T\tilde V^D .
--   $$
--
--   Hence the benchmark scales linearly in $k$, which fixes the size of the loss in the goal.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: scaling factor k ≥ 1 with T^k = kT, y^k = ky → every real k ≥ 1 with N = kT and Y_j = k y_j natural numbers, y real-valued; reason: it contains k ∈ ℕ with y ∈ ℕ^J, and the fractional y_j of the proof's T = 1 reduction
--   - encoding: V^{k,D} and V^D as max → detValue, a supremum; reason: the supremum is attained at the stationary schedule, as the statement shows
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, §7.1, p.22; (13), p.20

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- §7.1, p.22, with (13), p.20 (SSRN abstract_id=3362921): in the scaled setting a^D is still a stationary
optimal solution of DET and V^{k,D} = k V^D = k T Ṽ^D.

**Formalization Note** The scaling factor is real, with kT and k y_j integers. Ṽ^D is `statObjective M a`.
The inventories are the casts of `Y`. -/
theorem scaled_value (M : Instance J) (T : ℕ) (hT : 0 < T) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) (k : ℝ) (hk : 1 ≤ k) (N : ℕ)
    (Y : Fin J → ℕ) (hN : (N : ℝ) = k * T) (hY : ∀ j, (Y j : ℝ) = k * y j) :
    IsStationaryOptimal M N (fun j => (Y j : ℝ)) a ∧
      detValue M N (fun j => (Y j : ℝ)) = (N : ℝ) * statObjective M a ∧
      detValue M T y = (T : ℝ) * statObjective M a := by sorry

end CascadeCC
