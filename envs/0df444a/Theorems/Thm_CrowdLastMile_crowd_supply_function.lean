-- Prove2me | Theorems.Thm_CrowdLastMile_crowd_supply_function
-- name    : CrowdLastMile.crowd_supply_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:24:25.945998+00:00
-- url     : https://prove2.me/theorems/b9f0e709-0f20-4cca-8dce-e8a5af3e02b6
-- title:
--   Proof of Proposition 1, p.39 — the crowd supply function $w^*(P)$ (corrected: factor $1/N$ removed)
-- statement:
--   Fix $P>0$ and let $C_1$, $C_2$, $R$, $C$ be as in Problem (14), under the standing sign conditions. Then:
--
--   1. the participation constraint $wPC_1/(NC_2)\ge R/N$ holds if and only if
--   $$
--   w\ \ge\ w^*(P)=\frac{R\,C_2}{P\,C_1};
--   $$
--   2. the objective $w\mapsto PwC+(1-P)c_T$ is strictly increasing;
--   3. if $R>0$, then $w^*(P)>0$.
--
--   So for a fixed crowd share the optimal wage is $w^*(P)$, the crowd supply function.
--
--   Differences from the source:
--   - correction: w* = [(Σ_{i=1}^N μ^k_(i) + γ^k√N σ^k)/N]·C2/(P·C1) (Proposition 1, p.17, and p.39) → w*(P) = (Σ_{i=1}^N μ^k_(i) + γ^k√N σ^k)·C2/(P·C1), without the factor 1/N; reason: the printed wage violates the participation constraint of (14) for N ≥ 2: at N = 2, m = 2, q = 2, all μ^a = σ^a = μ^s = σ^s = 1, γ^a = γ^s = 1, γ^k = 2, β = 1, v_j = √3, μ^k = (18, 22), σ^k = 3, α = 10, ϵ = 0.1, c_T = 10, it gives w ≈ 16.16 at P* = 1 while the constraint needs w ≥ 32.32; for N = 1 the two formulas agree
--   - generalization: ϵ is smaller than any other number (p.10) → ϵ is any real number with 0 < ϵ < 1; reason: the statement holds for every such ϵ, which covers the paper's arbitrarily small ϵ
--   - generalization: β = β_U Σ_z √(p_z/Σ_j A_j p_j) A_z (p.10) → β is any positive real number; reason: the statement holds for every positive β, which covers the paper's value
--   - reading: c_T is the 3PL fee per package (p.6), with no stated sign → c_T > 0; reason: the proof's claim that the objective is decreasing in P (p.41), and uniqueness, need it; §5 uses positive fees
--   - encoding: means and standard deviations of times and costs, speeds, conservatism levels, without explicit signs → μ^a_ℓ > 0; σ^a_ℓ, σ^s_ℓ, σ^k > 0; μ^s_ℓ, μ^k_i ≥ 0; β > 0; v_j > 0; γ^a, γ^s, γ^k ≥ 0; reason: these exclude only undefined or meaningless instances (the standard deviations and N Σμ^a/m are divisors in the source); no sign is imposed on α
--   - encoding: w*(P) is only asserted to be the optimal wage in the domain w > 0 → the added clause R > 0 → w*(P) > 0; reason: it records that w*(P) lies in the domain w > 0 of (14)
--   - reading: the objective is an increasing function of w (p.39) → it is strictly increasing in w (StrictMono); reason: for P > 0 it is affine in w with slope P·C > 0, so it is increasing in the strict sense, the stronger reading
--   - encoding: 1-based indices, τ^m = m/N an integer, a^j = ⌈j/N⌉ − 1, j_i the j-th element of J_i, max_i {…} ≤ α → sequences ℕ → ℝ read on the printed ranges, m = τm·N, a^j = (j + N − 1)/N − 1 in ℕ, j_i = (i − 1)N + j, and ∀ i ∈ {1,…,a^j}, … ≤ α; reason: same instances: every index that occurs is in range, and a^j ≥ 1 for j ≥ N + 1 so the max is over a non-empty range
--   - encoding: order statistics μ^k_(1) ≤ … ≤ μ^k_(ℕ) → the first N entries of the sorted multiset of the means; reason: Lean convention; same value
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, proof of Proposition 1, p.39

import Mathlib
import Definitions.Def_CrowdLastMile_ClosedForms

namespace CrowdLastMile

/-- **The crowd supply function**, proof of Proposition 1, p.39 (Fatehi–Wagner, Crowdsourcing
Last-Mile Deliveries, SSRN 3434625), corrected. For `P > 0`: the participation constraint holds at
`(P, w)` if and only if `w ≥ w*(P)`; the objective is strictly increasing in `w`; and `w*(P) > 0`
when the right-hand side `R` of the participation constraint is positive. -/
theorem crowd_supply_function (p : Params) (hV : p.Valid) (P : ℝ) (hP : 0 < P) :
    (∀ w : ℝ, p.Participation P w ↔ p.wSupply P ≤ w) ∧
    StrictMono (fun w : ℝ => p.obj P w) ∧
    (0 < p.R → 0 < p.wSupply P) := by sorry

end CrowdLastMile
