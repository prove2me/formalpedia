-- Prove2me | Theorems.Thm_EPRPharma_sr_replicates_ec
-- name    : EPRPharma.sr_replicates_ec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:26:38.624012+00:00
-- url     : https://prove2.me/theorems/8f94eb2e-5d1d-44f5-973e-7e6efd203fb7
-- title:
--   SR replicates every over-prescribing EC equilibrium with $r_{SR}=r_{EC}$, $t=kr_{EC}/2$
-- statement:
--   Assume the standing assumptions. Let $(r_{EC},d)$ be an equilibrium of the EC model in which the producer's decision $d$ induces over-prescription. Then the SR policy
--
--   $$r_{SR}=r_{EC},\qquad t=\frac k2\,r_{EC},$$
--
--   together with the same decision $d$, is an equilibrium of the SR model, and it gives the same total welfare as the EC equilibrium.
--
--   With over-prescription the whole unit is dispensed and half of it is unused on average, so the fee $\frac k2 r_{EC}$ exactly covers the collection cost: the planner's surplus is zero and the producer's profit is unchanged, while the fee makes not over-prescribing no more attractive than under EC. This is the step of the proof of Proposition 4 showing that SR is at least as good as EC when EC cannot eliminate over-prescription.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: the planner maximizes W(y_P) subject to 0 ≤ r_P ≤ 1, t ≥ 0, Π*_m ≥ 0, Π_sp ≥ 0, anticipating the producer's optimal decision (pp. 11, 13) → IsEquilibrium: a feasible policy y with an optimal producer decision d, Π_m ≥ 0 and Π_sp ≥ 0; the planner may select among the producer's tied optimal decisions; reason: at r̄_EC and t̄ the producer is indifferent and the proof (App. p. 2) assigns r̄_EC to both regions; no uniqueness of the producer's response is assumed
--   - reading: no sign conditions printed on α, β, o_d, u_p, k, ε_e, ε_s → α, β, o_d, k > 0 and u_p, ε_e, ε_s ≥ 0 (Params.Standing); reason: α, β are quadratic cost constants and the proofs divide by α, β, k; u_p ≥ 0 is used in the proof of Lemma 1; ε_e ≥ 0 is necessary (α = β = o_d = 1: no equilibrium over-prescribes, so 'iff ε_e ≥ ε̄' has no real threshold on all of ℝ)
--   - encoding: an EC policy is r_EC; an SR policy is (r_SR, t) → a policy is a pair (r, t); an EC policy is (r_EC, 0); reason: no EC quantity reads t, so the instances are the same
--   - reading: over-prescription: 'prescription medicine beyond the need of the patient (q_p > θ_n)' (p. 10) → OverPrescribes: q*_p(θ_n) > θ_n for some θ_n ∈ [0, 1]; reason: the decision is fixed before θ_n is drawn; by Lemma 1 this is η_d ≥ p + o_d(1 − η_p)
--   - generalization: the replication r_SR = r_EC, t = (k/2) r_EC argued when u_p ≥ ū_p^SR and k < k̄ (App. p. 4) → every over-prescribing EC equilibrium (r, d) gives the SR equilibrium (r, k r/2) with the same d and the same welfare; reason: the argument uses only that the EC producer weakly prefers over-prescription at r; it specializes to the paper's case
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), proof of Proposition 4, Online Appendix p. 4 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_IsEquilibrium
import Definitions.Def_EPRPharma_OverPrescribes
import Definitions.Def_EPRPharma_welfare

namespace EPRPharma

/-- **SR replicates every over-prescribing EC equilibrium with r_SR = r_EC and t = k r_EC/2.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), proof of Proposition 4, Online
Appendix p. 4 (unnumbered): "We next prove that for any r_EC ∈ [0,1], the same welfare can be
achieved under the SR model by setting r_SR = r_EC and t = (k/2) r_EC, implying that the SR model is
at least as good as the EC model. [...] Moreover, when there is over-prescription, t = (k/2) r_EC
implies no deficit and no surplus, i.e., the collected fee is exactly equal to the collection cost.
Therefore, r_SR = r_EC and t = (k/2) r_EC is a feasible solution under the SR model and leads to the
same outcome as the EC model."

Under the standing assumptions, if (r, d) is an EC equilibrium in which d induces
over-prescription, then (r, k r/2) together with the same decision d is an SR equilibrium, and the
two give the same total welfare.

**Formalization Note.** The paper argues this in the case u_p ≥ ū_p^SR and k < k̄ (and α < 1/4,
β < o_d/2); the statement holds for every over-prescribing EC equilibrium (generalization). -/
theorem sr_replicates_ec (P : Params) (hP : P.Standing) (r : ℝ) (d : Decision)
    (heq : IsEquilibrium P .EC (r, 0) d) (hop : OverPrescribes P d) :
    IsEquilibrium P .SR (r, P.k * r / 2) d ∧
      welfare P .SR (r, P.k * r / 2) d = welfare P .EC (r, 0) d := by sorry

end EPRPharma
