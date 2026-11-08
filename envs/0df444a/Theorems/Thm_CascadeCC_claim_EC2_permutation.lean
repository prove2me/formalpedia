-- Prove2me | Theorems.Thm_CascadeCC_claim_EC2_permutation
-- name    : CascadeCC.claim_EC2_permutation
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:34:30.38299+00:00
-- url     : https://prove2.me/theorems/ffbf944e-9135-4b13-b18d-e73881d19c85
-- title:
--   Claim EC.2 — $W_j$ depends on $\sigma_j$ only through its sorted values
-- statement:
--   Let $W_j(\sigma)=R^D_j(\sigma,y)$. If $\sigma$ and $\sigma'$ have the same sorted values, then $W_j(\sigma)=W_j(\sigma')$. Equivalently, for every permutation $\pi$ of the periods and every inventory vector $z$,
--
--   $$
--   R^D_j(\sigma\circ\pi,z)=R^D_j(\sigma,z).
--   $$
--
--   This records that the periods of the deterministic problem are interchangeable.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - encoding: equal sorted vectors → a permutation of the periods; reason: two vectors with equal sorted values differ by a permutation
--   - generalization: W_j, that is, inventory y → every inventory vector z; reason: W_j is the case z = y
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Claim EC.2, p.ec7

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Claim EC.2, p.ec7 (SSRN abstract_id=3362921): W_j depends on σ_j only through its sorted
values.

**Formalization Note** Two vectors with equal sorted values differ by a permutation of the periods, so
the claim is invariance under every permutation. It is stated for every inventory vector `z`, W_j being
the case `z = y`. -/
theorem claim_EC2_permutation (M : Instance J) (n j : ℕ) (σ : Fin n → ℝ) (z : Fin J → ℝ)
    (π : Equiv.Perm (Fin n)) : Rev M n j (σ ∘ π) z = Rev M n j σ z := by sorry

end CascadeCC
