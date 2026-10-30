-- Prove2me | Theorems.Thm_EPRPharma_proposition_2_collection_cost_threshold
-- name    : EPRPharma.proposition_2_collection_cost_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:34.109575+00:00
-- url     : https://prove2.me/theorems/98d86e69-f35b-41ec-a7c3-ca97d3454fb7
-- title:
--   Proposition 2: a collection cost threshold $\bar k(u_p)$ under EC
-- statement:
--   There exists a collection cost threshold $\bar k$, a function of $(\alpha,\beta,o_d,u_p)$, such that, under the standing assumptions and whenever $u_p\ge\bar u_p^{EC}$ (that is, over-prescription can be eliminated under EC for some unit collection cost $k'>0$):
--
--   1. if $k<\bar k$, then for every collection rate $r_{EC}\in[0,1]$ the producer gains a strictly higher profit by inducing over-prescription;
--   2. over-prescription can be eliminated under EC if and only if $k\ge\bar k$.
--
--   When collection is cheap, the collection obligation of EC is too weak an incentive: dispensing more medicine pays for the collection of the unused part. The second clause is the identification of $\bar k$ on p. 17.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: the planner maximizes W(y_P) subject to 0 ≤ r_P ≤ 1, t ≥ 0, Π*_m ≥ 0, Π_sp ≥ 0, anticipating the producer's optimal decision (pp. 11, 13) → IsEquilibrium: a feasible policy y with an optimal producer decision d, Π_m ≥ 0 and Π_sp ≥ 0; the planner may select among the producer's tied optimal decisions; reason: at r̄_EC and t̄ the producer is indifferent and the proof (App. p. 2) assigns r̄_EC to both regions; no uniqueness of the producer's response is assumed
--   - reading: thresholds with suppressed arguments, ū_p^EC, ū_p^SR, k̄(u_p), ε̄_e(u_p,k), ε̃_e(u_p,k) (p. 15) → ū^EC, ū^SR functions of (α, β, o_d); k̄ of (α, β, o_d, u_p); ε̄^EC, ε̄^SR, ε̃ of (α, β, o_d, u_p, k, ε_s); reason: the paper writes k̄(u_p) and ε̄(u_p,k) and differentiates ε̄ in ε_s; no threshold depends on the variable it thresholds
--   - reading: thresholds 'as presented in Propositions 1, 2, 3' (p. 17) → the thresholds satisfy the printed properties of Propositions 1–3 and the p. 17 identification: over-prescription can be eliminated under EC iff u_p ≥ ū^EC and k ≥ k̄, under SR iff u_p ≥ ū^SR; reason: p. 17: 'the cases where over-prescription can be eliminated (i.e., u_p ≥ ū_p^EC and k ≥ k̄ under the EC model and u_p ≥ ū_p^SR under the SR model)'; without it ū = −1 and k̄ = 0 satisfy Propositions 1–2
--   - generalization: the proofs treat α < 1/4 and β < o_d/2 with r^i_EC, r^ii_EC ≥ 0 (App. pp. 2–5) → every α > 0 and β > 0; reason: the printed propositions carry no restriction on α, β and App. p. 1 gives the producer's optimum in all four (α, β) cases; the statement specializes to the paper's case
--   - reading: no sign conditions printed on α, β, o_d, u_p, k, ε_e, ε_s → α, β, o_d, k > 0 and u_p, ε_e, ε_s ≥ 0 (Params.Standing); reason: α, β are quadratic cost constants and the proofs divide by α, β, k; u_p ≥ 0 is used in the proof of Lemma 1; ε_e ≥ 0 is necessary (α = β = o_d = 1: no equilibrium over-prescribes, so 'iff ε_e ≥ ε̄' has no real threshold on all of ℝ)
--   - encoding: an EC policy is r_EC; an SR policy is (r_SR, t) → a policy is a pair (r, t); an EC policy is (r_EC, 0); reason: no EC quantity reads t, so the instances are the same
--   - reading: over-prescription: 'prescription medicine beyond the need of the patient (q_p > θ_n)' (p. 10) → OverPrescribes: q*_p(θ_n) > θ_n for some θ_n ∈ [0, 1]; reason: the decision is fixed before θ_n is drawn; by Lemma 1 this is η_d ≥ p + o_d(1 − η_p)
--   - reading: the hypothesis 'u_p ≥ ū_p^EC' → over-prescription can be eliminated under EC for some collection cost k' > 0; reason: by p. 17 and Proposition 1 (clause 5 of proposition_1_health_benefit_thresholds) this is u_p ≥ ū^EC; it keeps the item from referring to another item's existential threshold
--   - reading: 'the producer gains a higher profit by inducing over-prescription' → some feasible decision inducing over-prescription earns strictly more than every feasible decision that does not; reason: the comparison of the producer's best profits in the two regions (App. p. 2: Π^EC(ii)* > Π^EC(i)*), with the region-(ii) best attained
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Proposition 2, p. 16; identification p. 17; proof, Online Appendix p. 2

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_PolicyFeasible
import Definitions.Def_EPRPharma_OPStrictlyMoreProfitable
import Definitions.Def_EPRPharma_CanEliminate

namespace EPRPharma

/-- **Proposition 2: a collection cost threshold k̄(u_p) below which EC cannot eliminate
over-prescription.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Proposition 2, p. 16:
"Under the EC model, for any unit health benefit u_p ≥ ū_p^EC, there exists a unit collection cost
threshold k̄(u_p) such that if k < k̄, then for any r_EC ∈ [0,1], the producer gains a higher profit
by inducing over-prescription."
Identification, p. 17: over-prescription can be eliminated under EC iff "u_p ≥ ū_p^EC and k ≥ k̄".

There is a function k̄ of (α, β, o_d, u_p) such that, under the standing assumptions and when
u_p ≥ ū^EC (that is, over-prescription can be eliminated under EC for some collection cost
k' > 0): if k < k̄ then for every feasible EC policy over-prescription is strictly more profitable;
and over-prescription can be eliminated under EC iff k ≥ k̄.

**Formalization Note.** The hypothesis u_p ≥ ū_p^EC is written through its characterization in
Proposition 1 (`proposition_1_health_benefit_thresholds`, clause 5), so that this item does not
refer to another item's existential threshold. The iff is the p. 17 sharpness (without it k̄ = 0
would do, since k > 0). -/
theorem proposition_2_collection_cost_threshold :
    ∃ kbar : ℝ → ℝ → ℝ → ℝ → ℝ,
      ∀ P : Params, P.Standing →
        (∃ k' : ℝ, 0 < k' ∧ CanEliminate { P with k := k' } .EC) →
        (P.k < kbar P.alpha P.beta P.od P.up →
            ∀ y : ℝ × ℝ, PolicyFeasible .EC y → OPStrictlyMoreProfitable P .EC y) ∧
          (CanEliminate P .EC ↔ kbar P.alpha P.beta P.od P.up ≤ P.k) := by sorry

end EPRPharma
