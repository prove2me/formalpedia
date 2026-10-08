-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_truthful_weaklyMonotone
-- name    : CHMSPricing.UnitDemand.truthful_weaklyMonotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:32:34.891882+00:00
-- url     : https://prove2.me/theorems/25b4b0ec-b6d6-43c5-817d-ae7a94d3dba9
-- title:
--   App. B, p. 13 — truthful mechanisms for the BMUMD are weakly monotone
-- statement:
--   Let $\mathcal A$ be a truthful, individually rational deterministic mechanism for an instance of the Bayesian multi-parameter unit-demand setting with services $J$ grouped into $J_1, \dots, J_m$. Then $\mathcal A$ satisfies weak monotonicity (Definition 3): for every buyer $i$ and all value vectors $v^1, v^2$ of the type space with $v^1_j = v^2_j$ for $j \notin J_i$,
--   $$v^1_{\mathcal A_i(v^1)} + v^2_{\mathcal A_i(v^2)} \ge v^1_{\mathcal A_i(v^2)} + v^2_{\mathcal A_i(v^1)}.$$
--
--   This is the first step of the proof of Lemma 3: weak monotonicity is what makes the allocation rule of the copies mechanism monotone in each value.
--
--   **Formalization Note** Truthfulness is dominant-strategy incentive compatibility with misreports in the support (pin P3), so the inequality is stated for value vectors in the type space.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 13, App. B, proof of Lemma 3, sentence before Definition 3

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

/-- App. B, proof of Lemma 3, p. 13: truthful mechanisms for the BMUMD satisfy weak
monotonicity (Definition 3). -/
theorem truthful_weaklyMonotone {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (A : MultiMechanism J m)
    (hA : IsTruthfulMulti D 𝒥 owner A) :
    WeaklyMonotone D owner A := by sorry

end CHMSPricing.UnitDemand
