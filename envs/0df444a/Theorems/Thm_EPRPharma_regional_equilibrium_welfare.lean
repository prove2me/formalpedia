-- Prove2me | Theorems.Thm_EPRPharma_regional_equilibrium_welfare
-- name    : EPRPharma.regional_equilibrium_welfare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:11.613364+00:00
-- url     : https://prove2.me/theorems/59031af8-97f9-4d0d-b87c-ca266ee0f393
-- title:
--   Total welfare at the producer's optimum, with and without over-prescription
-- statement:
--   Assume the standing assumptions. Let $P\in\{EC,SR\}$, let $(r,t)$ be a feasible policy of $P$ and let $d$ be an optimal decision of the producer under $(P,(r,t))$.
--
--   1. If $d$ does not induce over-prescription, then
--   $$W=\Pi_m+\Pi_{sp}-\epsilon_e\Big(\frac13+\frac{1-r}6\Big)-\epsilon_s\,\frac{1-r}6 .$$
--   2. If $d$ induces over-prescription, then
--   $$W=\frac{u_p+o_d(1-\eta_p)}2+\Pi_m+\Pi_{sp}-\epsilon_e\Big(\frac12+\frac{1-r}2\Big)-\epsilon_s\,\frac{1-r}2 .$$
--
--   Moreover, for every decision $d$ and every pair $(r,t)$, the SR planner's surplus is $\Pi_{sp}=\frac t2-\frac{kr}6$ when $d$ does not induce over-prescription and $\Pi_{sp}=t-\frac{kr}2$ when it does (under EC, $\Pi_{sp}=0$).
--
--   In the case $\alpha<1/4$, $\beta<o_d/2$ these reduce to the paper's $W^{EC(i)*}(r_{EC})=\frac{3-6\alpha-(3-r_{EC})\epsilon_e-(1-r_{EC})\epsilon_s-kr_{EC}+3u_p}6$ and $W^{EC(ii)*}(r_{EC})=\frac{2(1-\alpha-\beta)-(2-r_{EC})\epsilon_e-(1-r_{EC})\epsilon_s-kr_{EC}+u_p}2$. They turn the planner's problem into the maximization of functions affine in the collection rate, region by region.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: no sign conditions printed on α, β, o_d, u_p, k, ε_e, ε_s → α, β, o_d, k > 0 and u_p, ε_e, ε_s ≥ 0 (Params.Standing); reason: α, β are quadratic cost constants and the proofs divide by α, β, k; u_p ≥ 0 is used in the proof of Lemma 1; ε_e ≥ 0 is necessary (α = β = o_d = 1: no equilibrium over-prescribes, so 'iff ε_e ≥ ε̄' has no real threshold on all of ℝ)
--   - encoding: an EC policy is r_EC; an SR policy is (r_SR, t) → a policy is a pair (r, t); an EC policy is (r_EC, 0); reason: no EC quantity reads t, so the instances are the same
--   - reading: over-prescription: 'prescription medicine beyond the need of the patient (q_p > θ_n)' (p. 10) → OverPrescribes: q*_p(θ_n) > θ_n for some θ_n ∈ [0, 1]; reason: the decision is fixed before θ_n is drawn; by Lemma 1 this is η_d ≥ p + o_d(1 − η_p)
--   - generalization: W^EC(i)*(r_EC), W^EC(ii)*(r_EC) and W^SR(ii) under α < 1/4, β < o_d/2 (App. pp. 2–3), with E[U_d] = u_p/2 in region (ii) → for every α, β > 0, both models and every optimal decision: W = Π_m + Π_sp − DU terms, with E[U_d] = 0 in region (i) and (u_p + o_d(1 − η_p))/2 in region (ii); the SR surplus formulas for every decision; reason: the printed displays are this statement at η*_p = 1 with the profits of the paper's case substituted
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), proofs of Propositions 3 and 4, Online Appendix pp. 2–3 and p. 5 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_PolicyFeasible
import Definitions.Def_EPRPharma_IsProducerOptimal
import Definitions.Def_EPRPharma_OverPrescribes
import Definitions.Def_EPRPharma_welfare

namespace EPRPharma

/-- **Total welfare at the producer's optimum, with and without over-prescription.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), proofs of Propositions 3 and 4,
Online Appendix pp. 2–3 (unnumbered): region (i): "E_θn[U_d^(i)*(θ_n)] = 0; [...]
DU_e^EC(i)*(r_EC) = ε_e(1/3 + (1−r_EC)/6) and DU_s^EC(i)*(r_EC) = ε_s (1−r_EC)/6 [...] Further, given
Π_m^EC(i)*(r_EC) = (3−6α−kr_EC+3u_p)/6, we have W^EC(i)*(r_EC) =
(3−6α−(3−r_EC)ε_e−(1−r_EC)ε_s−kr_EC+3u_p)/6"; region (ii): "E_θn[U_d^(ii)*(1)] = [...] = u_p/2;
DU_e^EC(ii)*(r_EC) = ε_e (1/2 + (1 − r_EC) 1/2) and DU_s^EC(ii)*(r_EC) = ε_s (1 − r_EC) 1/2 [...]
Further, given Π_m^EC(ii)*(r_EC) = 1 − α − β − kr_EC/2, we have W^EC(ii)*(r_EC) =
(2(1−α−β)−(2−r_EC)ε_e−(1−r_EC)ε_s−kr_EC+u_p)/2"; under SR (p. 3) the planner's surplus is
t − k r_SR/2 with over-prescription (the constraint "(1/2) k r_SR ≤ t") and t/2 − k r_SR/6 without
(p. 5: "(1/6) k r_SR ≤ (1/2) t").

Under the standing assumptions, for either model, every feasible policy (r, t) and every optimal
decision d of the producer:
1. if d does not induce over-prescription, then
   W = Π_m + Π_sp − ε_e(1/3 + (1 − r)/6) − ε_s(1 − r)/6;
2. if d induces over-prescription, then
   W = (u_p + o_d(1 − η_p))/2 + Π_m + Π_sp − ε_e(1/2 + (1 − r)/2) − ε_s(1 − r)/2;

and, for every decision d and every (r, t), the SR planner's surplus is t/2 − kr/6 without and
t − kr/2 with over-prescription.

**Formalization Note.** The printed displays assume α < 1/4 and β < o_d/2, where η*_p = 1 and the
doctor's expected utility in region (ii) is u_p/2; the statement covers every α, β > 0 with the
doctor's expected utility (u_p + o_d(1 − η_p))/2 (generalization). -/
theorem regional_equilibrium_welfare (P : Params) (hP : P.Standing) :
    (∀ (m : Model) (r t : ℝ) (d : Decision), PolicyFeasible m (r, t) →
      IsProducerOptimal P m (r, t) d →
      (¬ OverPrescribes P d →
        welfare P m (r, t) d = producerProfit P m (r, t) d + plannerSurplus P m (r, t) d
          - P.epsE * (1 / 3 + (1 - r) / 6) - P.epsS * (1 - r) / 6) ∧
      (OverPrescribes P d →
        welfare P m (r, t) d = (P.up + P.od * (1 - d.etaP)) / 2 + producerProfit P m (r, t) d
          + plannerSurplus P m (r, t) d - P.epsE * (1 / 2 + (1 - r) / 2) - P.epsS * (1 - r) / 2)) ∧
    (∀ (r t : ℝ) (d : Decision),
      (¬ OverPrescribes P d → plannerSurplus P .SR (r, t) d = t / 2 - P.k * r / 6) ∧
      (OverPrescribes P d → plannerSurplus P .SR (r, t) d = t - P.k * r / 2)) := by sorry

end EPRPharma
