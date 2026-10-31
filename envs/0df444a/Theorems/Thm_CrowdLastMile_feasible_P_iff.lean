-- Prove2me | Theorems.Thm_CrowdLastMile_feasible_P_iff
-- name    : CrowdLastMile.feasible_P_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:24:29.073012+00:00
-- url     : https://prove2.me/theorems/6a13ebd2-aac5-47e3-ad8b-e16c365d4ecf
-- title:
--   Proof of Proposition 1, pp.40–41 — Problem (21): the feasible crowd shares (corrected: hypothesis $E^j_i\ge0$)
-- statement:
--   Assume $\alpha>\max_{j=1,\dots,m}F^j_{i=0}$ and $E^j_i\ge0$ for every $j\in\{N+1,\dots,m\}$ and $i\in\{1,\dots,a^j\}$ with $F^j_i\le\alpha$. Then a real number $P$ admits a $w$ with $(P,w)$ feasible for Problem (14) if and only if $P>0$ and
--
--   $$
--   \hat P\le P\le\min\{\bar P^N,\tilde P,1\}.
--   $$
--
--   This reduces Problem (14) to the one-dimensional Problem (21) in the crowd share $P$.
--
--   Differences from the source:
--   - correction: no hypothesis; the proof (p.40) asserts E^j_i = min_{A∈U_A(P)} Σ A_ℓ ≥ 0 → hypothesis E^j_i ≥ 0 for every j ∈ {N+1,…,m} and i ∈ {1,…,a^j} with F^j_i ≤ α; reason: E^j_i is not that minimum and can be negative, and then the result is false: at q = 1, N = 1, m = 2, μ^a = σ^a = μ^s = σ^s = 1, γ^a = γ^s = 2, β = 1, v_j = √2, α = 7.5, ϵ = 0.1 the printed condition holds with P* = 0.45, but j = 2, i = 1 forces P ≥ 1.49, so (14) is infeasible
--   - generalization: ϵ is smaller than any other number (p.10) → ϵ is any real number with 0 < ϵ < 1; reason: the statement holds for every such ϵ, which covers the paper's arbitrarily small ϵ
--   - generalization: β = β_U Σ_z √(p_z/Σ_j A_j p_j) A_z (p.10) → β is any positive real number; reason: the statement holds for every positive β, which covers the paper's value
--   - reading: c_T is the 3PL fee per package (p.6), with no stated sign → c_T > 0; reason: the proof's claim that the objective is decreasing in P (p.41), and uniqueness, need it; §5 uses positive fees
--   - reading: P̄^N = min_{j=N+1,…,m} min_{i∈s^j_2} E^j_i/(F^j_i − α), with no convention for empty sets → a minimum over an empty set is +∞, computed in WithTop ℝ, so P* = min{P̃, 1} when every s^j_2 is empty and in particular when m = N; reason: this is the only reading under which the proposition covers such instances, and the proof's constraint P ≤ min_{i∈s^j_2} is then vacuous
--   - encoding: means and standard deviations of times and costs, speeds, conservatism levels, without explicit signs → μ^a_ℓ > 0; σ^a_ℓ, σ^s_ℓ, σ^k > 0; μ^s_ℓ, μ^k_i ≥ 0; β > 0; v_j > 0; γ^a, γ^s, γ^k ≥ 0; reason: these exclude only undefined or meaningless instances (the standard deviations and N Σμ^a/m are divisors in the source); no sign is imposed on α
--   - encoding: 1-based indices, τ^m = m/N an integer, a^j = ⌈j/N⌉ − 1, j_i the j-th element of J_i, max_i {…} ≤ α → sequences ℕ → ℝ read on the printed ranges, m = τm·N, a^j = (j + N − 1)/N − 1 in ℕ, j_i = (i − 1)N + j, and ∀ i ∈ {1,…,a^j}, … ≤ α; reason: same instances: every index that occurs is in range, and a^j ≥ 1 for j ≥ N + 1 so the max is over a non-empty range
--   - reading: Problem (21), "min_P … s.t. P̂ ≤ P ≤ min{P̄^N, P̃, 1}", obtained from (19)–(20) by substituting w = w*(P), over the domain P ∈ (0,1] of (19) → the set of P for which some w makes (P, w) feasible for (14) is {P : 0 < P ∧ P̂ ≤ P ∧ P ≤ min{P̄^N, P̃, 1}}; reason: w enters (14) only through the participation constraint, which some w > 0 satisfies for every P > 0, so the feasible P of (14) are those of (20); 0 < P restates the domain of (19), and P ≤ 1 is inside the min
--   - encoding: order statistics μ^k_(1) ≤ … ≤ μ^k_(ℕ) → the first N entries of the sorted multiset of the means; reason: Lean convention; same value
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, proof of Proposition 1, eq. (21), pp.40–41

import Mathlib
import Definitions.Def_CrowdLastMile_ClosedForms

namespace CrowdLastMile

/-- **Problem (21): the feasible crowd shares**, proof of Proposition 1, pp.40–41 (Fatehi–Wagner,
Crowdsourcing Last-Mile Deliveries, SSRN 3434625), corrected. If `α > max_j F^j_{i=0}` and `E^j_i ≥ 0`
for the pairs `(j, i)` with `F^j_i ≤ α`, then a real number `P` is the crowd share of a feasible point
of Problem (14) if and only if `P > 0` and `P̂ ≤ P ≤ min{P̄^N, P̃, 1}`. -/
theorem feasible_P_iff (p : Params) (hV : p.Valid) (hα : p.maxF0 < p.α) (hE : p.HE) (P : ℝ) :
    (∃ w : ℝ, p.Feasible P w) ↔ 0 < P ∧ p.PHat ≤ P ∧ P ≤ p.PStar := by sorry

end CrowdLastMile
