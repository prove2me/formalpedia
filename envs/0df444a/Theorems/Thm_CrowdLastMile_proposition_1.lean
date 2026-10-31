-- Prove2me | Theorems.Thm_CrowdLastMile_proposition_1
-- name    : CrowdLastMile.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:24:38.429733+00:00
-- url     : https://prove2.me/theorems/2f7750c1-18d3-48ef-8f2c-3da2e06a5cbf
-- title:
--   Proposition 1, p.17 — optimal crowd share $P^*$ and wage $w^*$ of Problem (14) (corrected: $w^*$; hypotheses on $E^j_i$ and $R$; clause $P^*>0$)
-- statement:
--   Consider Problem (14), and assume $\alpha>\max_{j=1,\dots,m}F^j_{i=0}$ and $E^j_i\ge0$ for every $j\in\{N+1,\dots,m\}$ and $i\in\{1,\dots,a^j\}$ with $F^j_i\le\alpha$. Let $P^*=\min\{\bar P^N,\tilde P,1\}$.
--
--   1. Problem (14) is feasible if and only if
--   $$
--   \hat P\le\min\{\bar P^N,\tilde P,1\}\quad\text{and}\quad\min\{\bar P^N,\tilde P,1\}>0 .
--   $$
--   2. If Problem (14) is feasible and $R=\sum_{i=1}^{N}\mu^k_{(i)}+\gamma^k\sqrt N\sigma^k>0$, then the pair $(P^*,w^*)$ with
--   $$
--   w^*=\frac{R\,C_2}{P^*C_1}
--   $$
--   is feasible, minimizes the objective over all feasible $(P,w)$, is the only minimizer, and the minimized worst-case delivery cost rate is
--   $$
--   z(N)=P^*\,(w^*C-c_T)+c_T .
--   $$
--
--   Here $\hat P$ is the lower bound from the formation of sets, $\bar P^N$ the upper bound from a driver's earlier sets, $\tilde P$ the stability bound, and $w^*$ makes the participation constraint bind. This is the closed-form solution of the robust crowdsourcing model.
--
--   Differences from the source:
--   - correction: w* = [(Σ_{i=1}^N μ^k_(i) + γ^k√N σ^k)/N]·C2/(P·C1) (Proposition 1, p.17, and p.39) → w*(P) = (Σ_{i=1}^N μ^k_(i) + γ^k√N σ^k)·C2/(P·C1), without the factor 1/N; reason: the printed wage violates the participation constraint of (14) for N ≥ 2: at N = 2, m = 2, q = 2, all μ^a = σ^a = μ^s = σ^s = 1, γ^a = γ^s = 1, γ^k = 2, β = 1, v_j = √3, μ^k = (18, 22), σ^k = 3, α = 10, ϵ = 0.1, c_T = 10, it gives w ≈ 16.16 at P* = 1 while the constraint needs w ≥ 32.32; for N = 1 the two formulas agree
--   - correction: no hypothesis; the proof (p.40) asserts E^j_i = min_{A∈U_A(P)} Σ A_ℓ ≥ 0 → hypothesis E^j_i ≥ 0 for every j ∈ {N+1,…,m} and i ∈ {1,…,a^j} with F^j_i ≤ α; reason: E^j_i is not that minimum and can be negative, and then the result is false: at q = 1, N = 1, m = 2, μ^a = σ^a = μ^s = σ^s = 1, γ^a = γ^s = 2, β = 1, v_j = √2, α = 7.5, ϵ = 0.1 the printed condition holds with P* = 0.45, but j = 2, i = 1 forces P ≥ 1.49, so (14) is infeasible
--   - correction: (14) is feasible iff P̂ ≤ min{P̄^N, P̃, 1} → (14) is feasible iff P̂ ≤ min{P̄^N, P̃, 1} and 0 < min{P̄^N, P̃, 1}; reason: P ∈ (0,1] excludes P = 0: at q = 1, N = 1, m = 2, μ^a = 2, σ^a = μ^s = σ^s = 1, γ^a = γ^s = 2, β = 1, v_j = √2, α = 6, ϵ = 0.1 one has P̂ = 0 = P̄^N, so the printed condition holds, but (14) is infeasible; the clause is implied when q ≥ 2
--   - correction: if feasible, the optimal solution is (P*, w*) → if feasible and R = Σ_{i=1}^N μ^k_(i) + γ^k√N σ^k > 0, the optimal solution is (P*, w*); reason: if R = 0 (for instance γ^k = 0 and the N cheapest means are 0), every w > 0 satisfies the participation constraint, the infimum over w > 0 is not attained and w* = 0 is not admissible; R > 0 holds whenever γ^k > 0
--   - generalization: ϵ is smaller than any other number (p.10) → ϵ is any real number with 0 < ϵ < 1; reason: the statement holds for every such ϵ, which covers the paper's arbitrarily small ϵ
--   - generalization: β = β_U Σ_z √(p_z/Σ_j A_j p_j) A_z (p.10) → β is any positive real number; reason: the statement holds for every positive β, which covers the paper's value
--   - reading: c_T is the 3PL fee per package (p.6), with no stated sign → c_T > 0; reason: the proof's claim that the objective is decreasing in P (p.41), and uniqueness, need it; §5 uses positive fees
--   - reading: P̄^N = min_{j=N+1,…,m} min_{i∈s^j_2} E^j_i/(F^j_i − α), with no convention for empty sets → a minimum over an empty set is +∞, computed in WithTop ℝ, so P* = min{P̃, 1} when every s^j_2 is empty and in particular when m = N; reason: this is the only reading under which the proposition covers such instances, and the proof's constraint P ≤ min_{i∈s^j_2} is then vacuous
--   - encoding: means and standard deviations of times and costs, speeds, conservatism levels, without explicit signs → μ^a_ℓ > 0; σ^a_ℓ, σ^s_ℓ, σ^k > 0; μ^s_ℓ, μ^k_i ≥ 0; β > 0; v_j > 0; γ^a, γ^s, γ^k ≥ 0; reason: these exclude only undefined or meaningless instances (the standard deviations and N Σμ^a/m are divisors in the source); no sign is imposed on α
--   - encoding: 1-based indices, τ^m = m/N an integer, a^j = ⌈j/N⌉ − 1, j_i the j-th element of J_i, max_i {…} ≤ α → sequences ℕ → ℝ read on the printed ranges, m = τm·N, a^j = (j + N − 1)/N − 1 in ℕ, j_i = (i − 1)N + j, and ∀ i ∈ {1,…,a^j}, … ≤ α; reason: same instances: every index that occurs is in range, and a^j ≥ 1 for j ≥ N + 1 so the max is over a non-empty range
--   - encoding: order statistics μ^k_(1) ≤ … ≤ μ^k_(ℕ) → the first N entries of the sorted multiset of the means; reason: Lean convention; same value
--   - encoding: the optimal solution is P*, with w*, and minimized cost z(N) → (P*, w*) is feasible, minimizes the objective over all feasible points, is the only minimizer, and has objective value z(N); reason: this spells out the definite article; nothing is dropped
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, Proposition 1, p.17; proof, pp.39–41

import Mathlib
import Definitions.Def_CrowdLastMile_ClosedForms

namespace CrowdLastMile

/-- **Proposition 1**, p.17 (Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625),
corrected. Assume `α > max_j F^j_{i=0}` and `E^j_i ≥ 0` for the pairs `(j, i)` with `F^j_i ≤ α`. Then
Problem (14) is feasible if and only if `P̂ ≤ min{P̄^N, P̃, 1}` and `min{P̄^N, P̃, 1} > 0`. If it is
feasible and the participation right-hand side `R` is positive, then `(P*, w*)` is feasible, it
minimizes the objective over all feasible points, it is the only minimizer, and the minimum
is `z(N)`.

**Formalization Note.** `w*` is the corrected wage of `Params.wSupply`. -/
theorem proposition_1 (p : Params) (hV : p.Valid) (hα : p.maxF0 < p.α) (hE : p.HE) :
    ((∃ P w : ℝ, p.Feasible P w) ↔ p.PHat ≤ p.PStar ∧ 0 < p.PStar) ∧
    (0 < p.R → (∃ P w : ℝ, p.Feasible P w) →
      p.Feasible p.PStar p.wStar ∧
      (∀ P w : ℝ, p.Feasible P w → p.obj p.PStar p.wStar ≤ p.obj P w) ∧
      (∀ P w : ℝ, p.Feasible P w → p.obj P w = p.obj p.PStar p.wStar →
        P = p.PStar ∧ w = p.wStar) ∧
      p.obj p.PStar p.wStar = p.zN) := by sorry

end CrowdLastMile
