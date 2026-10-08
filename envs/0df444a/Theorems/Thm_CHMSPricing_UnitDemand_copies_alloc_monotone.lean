-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_copies_alloc_monotone
-- name    : CHMSPricing.UnitDemand.copies_alloc_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:32:38.145815+00:00
-- url     : https://prove2.me/theorems/0c8d07e3-8e28-4406-9fbd-c370ced49b2c
-- title:
--   App. B, p. 13 — the allocation rule of $\mathcal A^{\mathrm{copies}}$ is monotone non-decreasing in each $v_j$
-- statement:
--   Let $\mathcal A$ be a truthful, individually rational deterministic mechanism for a BMUMD instance with a unit-demand set system $\mathcal J$. The mechanism $\mathcal A^{\mathrm{copies}}$ for the instance with copies serves copy $j$ exactly when $\mathcal A$ allocates service $j$. Its allocation rule is monotone non-decreasing in each $v_j$: for every value vector $v$ of the type space, every service $j$ and all $x \le y$ in the support of $F_j$,
--   $$j \in \mathcal A(v_{-j}, x) \implies j \in \mathcal A(v_{-j}, y),$$
--   where $(v_{-j}, x)$ is $v$ with its $j$-th coordinate replaced by $x$.
--
--   By the single-parameter characterization of truthfulness, this monotonicity is what allows threshold payments that make $\mathcal A^{\mathrm{copies}}$ truthful, the construction behind Lemma 3.
--
--   **Formalization Note** The paper states the claim as $(x - y)(\alpha_x - \alpha_y) \ge 0$ for the probabilities of service; for a deterministic mechanism these are $0$ or $1$, which gives the implication above. The unit-demand property of $\mathcal J$ is a hypothesis, as in the BMUMD.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 13, App. B, proof of Lemma 3, paragraph after Definition 3

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

/-- App. B, proof of Lemma 3, p. 13: the allocation rule of `𝒜^copies` (which serves the copy
`j` exactly when `𝒜` allocates service `j`) is monotone non-decreasing in each `v_j`: raising
`v_j` within its support, all other values fixed, never withdraws service `j`. -/
theorem copies_alloc_monotone {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A)
    (v : J → ℝ) (hv : v ∈ typeSpace D) (j : J) (x y : ℝ)
    (hx : x ∈ Set.Icc (D j).lo (D j).hi) (hy : y ∈ Set.Icc (D j).lo (D j).hi) (hxy : x ≤ y)
    (hj : j ∈ A.alloc (Function.update v j x)) :
    j ∈ A.alloc (Function.update v j y) := by sorry

end CHMSPricing.UnitDemand
