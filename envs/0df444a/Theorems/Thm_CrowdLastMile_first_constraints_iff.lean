-- Prove2me | Theorems.Thm_CrowdLastMile_first_constraints_iff
-- name    : CrowdLastMile.first_constraints_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:24:55.581725+00:00
-- url     : https://prove2.me/theorems/b2de2ba0-1f30-413f-8143-64bee7e32224
-- title:
--   Proof of Proposition 1, p.40 — the constraints for $j>N$ (corrected: hypothesis $E^j_i\ge0$)
-- statement:
--   Let $P>0$.
--
--   1. For $j\in\{N+1,\dots,m\}$ such that $E^j_i\ge0$ for every $i\in\{1,\dots,a^j\}$ with $F^j_i\le\alpha$, the first constraint of Problem (14) for this $j$ holds if and only if
--   $$
--   P\le\frac{E^j_i}{F^j_i-\alpha}\qquad\text{for every } i\in s^j_2 .
--   $$
--   2. If this hypothesis holds for every $j\in\{N+1,\dots,m\}$, the whole first family holds if and only if $P\le\bar P^N$.
--
--   These constraints say that the sets a driver served earlier leave the driver free in time; only the indices in $s^j_2$ bound $P$.
--
--   Differences from the source:
--   - correction: no hypothesis; the proof (p.40) asserts E^j_i = min_{A∈U_A(P)} Σ A_ℓ ≥ 0 → hypothesis E^j_i ≥ 0 for every j ∈ {N+1,…,m} and i ∈ {1,…,a^j} with F^j_i ≤ α; reason: E^j_i is not that minimum and can be negative, and then the result is false: at q = 1, N = 1, m = 2, μ^a = σ^a = μ^s = σ^s = 1, γ^a = γ^s = 2, β = 1, v_j = √2, α = 7.5, ϵ = 0.1 the printed condition holds with P* = 0.45, but j = 2, i = 1 forces P ≥ 1.49, so (14) is infeasible
--   - generalization: the model's standing assumptions on the data → no assumption on the data beyond P > 0 and the hypothesis on E^j_i; reason: the argument uses no sign of the data, so the statement covers the paper's instances
--   - reading: P̄^N = min_{j=N+1,…,m} min_{i∈s^j_2} E^j_i/(F^j_i − α), with no convention for empty sets → a minimum over an empty set is +∞, computed in WithTop ℝ, so P* = min{P̃, 1} when every s^j_2 is empty and in particular when m = N; reason: this is the only reading under which the proposition covers such instances, and the proof's constraint P ≤ min_{i∈s^j_2} is then vacuous
--   - encoding: 1-based indices, τ^m = m/N an integer, a^j = ⌈j/N⌉ − 1, j_i the j-th element of J_i, max_i {…} ≤ α → sequences ℕ → ℝ read on the printed ranges, m = τm·N, a^j = (j + N − 1)/N − 1 in ℕ, j_i = (i − 1)N + j, and ∀ i ∈ {1,…,a^j}, … ≤ α; reason: same instances: every index that occurs is in range, and a^j ≥ 1 for j ≥ N + 1 so the max is over a non-empty range
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, proof of Proposition 1, p.40

import Mathlib
import Definitions.Def_CrowdLastMile_ClosedForms

open Finset

namespace CrowdLastMile

/-- **The constraints for `j > N`**, proof of Proposition 1, p.40 (Fatehi–Wagner, Crowdsourcing
Last-Mile Deliveries, SSRN 3434625), corrected. For `P > 0`: under `E^j_i ≥ 0` for the `i` with
`F^j_i ≤ α`, the first constraint of Problem (14) for a set `j ∈ {N+1, …, m}` holds if and only if
`P ≤ E^j_i / (F^j_i - α)` for every `i ∈ s^j_2`; and if this hypothesis holds for every such `j`, the
whole first family holds if and only if `P ≤ P̄^N`. -/
theorem first_constraints_iff (p : Params) (P : ℝ) (hP : 0 < P) :
    (∀ j ∈ Icc (p.N + 1) p.m, p.HEAt j →
      ((∀ i ∈ Icc 1 (p.a j), p.firstTerm P j i ≤ p.α) ↔
        ∀ i ∈ p.s2 j, P ≤ p.E j i / (p.F j i - p.α))) ∧
    (p.HE → (p.FirstFamily P ↔ (P : WithTop ℝ) ≤ p.PBar)) := by sorry

end CrowdLastMile
