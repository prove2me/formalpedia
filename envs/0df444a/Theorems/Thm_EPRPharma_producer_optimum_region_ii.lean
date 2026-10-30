-- Prove2me | Theorems.Thm_EPRPharma_producer_optimum_region_ii
-- name    : EPRPharma.producer_optimum_region_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:09.572402+00:00
-- url     : https://prove2.me/theorems/f00d9a54-93c0-4460-badc-8d2f345e15be
-- title:
--   The producer's best decision with over-prescription (region (ii)), all four $(\alpha,\beta)$ cases
-- statement:
--   Assume the standing assumptions. Among the feasible decisions that induce over-prescription, the producer's profit is maximized, under either model and for every policy $(r,t)$, by $p^*=\eta_d^*+o_d\eta_p^*-o_d$ with
--
--   1. $\alpha<\tfrac12$, $\beta<\tfrac{o_d}2$: $p^*=\eta_d^*=\eta_p^*=1$, $\;\Pi_m^{EC(ii)*}(r)=1-\alpha-\beta-\tfrac{kr}2$, $\;\Pi_m^{SR(ii)*}(t)=1-\alpha-\beta-t$;
--   2. $\alpha<\tfrac12$, $\beta\ge\tfrac{o_d}2$: $p^*=1-o_d+\tfrac{o_d^2}{2\beta}$, $\eta_d^*=1$, $\eta_p^*=\tfrac{o_d}{2\beta}$, $\;\Pi_m^{EC(ii)*}(r)=\tfrac{o_d^2-2\beta(2\alpha+kr+2(-1+o_d))}{4\beta}$, $\;\Pi_m^{SR(ii)*}(t)=\tfrac{o_d^2+4\beta(1-\alpha-o_d-t)}{4\beta}$;
--   3. $\alpha\ge\tfrac12$, $\beta<\tfrac{o_d}2$: $p^*=\eta_d^*=\tfrac1{2\alpha}$, $\eta_p^*=1$, $\;\Pi_m^{EC(ii)*}(r)=\tfrac14\big(\tfrac1\alpha-2(2\beta+kr)\big)$, $\;\Pi_m^{SR(ii)*}(t)=\tfrac{1-4\alpha(\beta+t)}{4\alpha}$;
--   4. $\alpha\ge\tfrac12$, $\beta\ge\tfrac{o_d}2$: $p^*=\tfrac12\big(\tfrac1\alpha+\tfrac{o_d(o_d-2\beta)}\beta\big)$, $\eta_d^*=\tfrac1{2\alpha}$, $\eta_p^*=\tfrac{o_d}{2\beta}$, $\;\Pi_m^{EC(ii)*}(r)=\tfrac14\big(\tfrac1\alpha-2kr-4o_d+\tfrac{o_d^2}\beta\big)$, $\;\Pi_m^{SR(ii)*}(t)=\tfrac14\big(\tfrac1\alpha+\tfrac{o_d^2-4\beta(o_d+t)}\beta\big)$.
--
--   In each case the stated decision is feasible and induces over-prescription. Together with region (i) this gives the producer's optimum for every parameter vector, which is what extends the paper's results beyond the case $\alpha<1/4$, $\beta<o_d/2$ treated in its proofs.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: region (ii): '(ii) η_d ≥ o_d(1 − η_p)' and 'p + o_d(1 − η_p) ≤ η_d', 0 ≤ η_d, η_p ≤ 1 (App. p. 1) → the feasible decisions that induce over-prescription; reason: the first description omits p (the next sentence has p + o_d(1 − η_p) ≤ η_d); by Lemma 1 and participation the sets coincide
--   - generalization: Π^EC(·)*_m(r_EC) for r_EC ∈ [0,1] and Π^SR(·)*_m(t) for t ≥ 0 → the optimality and the profit formulas for every model and every real pair (r, t); reason: the optimum in a region does not depend on the policy and the profits are affine in r and t; the statement specializes to feasible policies
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), proof of Propositions 1–2, Region (ii), Online Appendix p. 1 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_producerProfit
import Definitions.Def_EPRPharma_DecisionFeasible
import Definitions.Def_EPRPharma_OverPrescribes

namespace EPRPharma

/-- **The producer's optimum with over-prescription (region (ii)), all four (α, β) cases.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), proof of Propositions 1–2, Online
Appendix p. 1 (unnumbered): "Region (ii): Set p,η_d,η_p such that p + o_d(1 − η_p) ≤ η_d to have
q*_p(p,η_d,η_p) = 1. [...] The producer's profit is increasing in p. Therefore, we must have
p* = η*_d + o_d η*_p − o_d at the optimal solution. Then, we can identify the optimal solution by
using first-order conditions: if α < 1/2 and β < o_d/2, p* = η*_d = η*_p = 1, and
Π_m^EC(ii)*(r_EC) = 1 − α − β − kr_EC/2 [Π_m^SR(ii)*(t) = 1 − α − β − t]; if α < 1/2 and β ≥ o_d/2,
p* = 1 − o_d + o_d²/(2β), η*_d = 1, η*_p = o_d/(2β), and Π_m^EC(ii)*(r_EC) =
(o_d² − 2β (2α + kr_EC + 2(−1 + o_d)))/(4β) [Π_m^SR(ii)*(t) = (o_d² + 4β (1 − α − o_d − t))/(4β)];
if α ≥ 1/2 and β < o_d/2, p* = 1/(2α), η*_d = 1/(2α), η*_p = 1, and Π_m^EC(ii)*(r_EC) =
(1/4)(1/α − 2(2β + kr_EC)) [Π_m^SR(ii)*(t) = (1 − 4α (β + t))/(4α)]; and if α ≥ 1/2 and
β ≥ o_d/2, p* = (1/2)(1/α + o_d(o_d − 2β)/β), η*_d = 1/(2α), η*_p = o_d/(2β), and
Π_m^EC(ii)*(r_EC) = (1/4)(1/α − 2kr_EC − 4o_d + o_d²/β) [Π_m^SR(ii)*(t) =
(1/4)(1/α + (o_d² − 4β (o_d + t))/β)]."

Under the standing assumptions, in each of the four cases the stated decision d₂ is feasible,
induces over-prescription, maximizes the producer's profit over all feasible decisions that induce
over-prescription (under either model and every policy), and earns the stated profits.

**Formalization Note.** The region is η_d ≥ p + o_d(1 − η_p); the appendix's first description of
it, "(ii) η_d ≥ o_d(1 − η_p)", omits p, as the next sentence's "p + o_d(1 − η_p) ≤ η_d" shows.
Stated for every policy pair (r, t): the EC profit does not depend on t, the SR profit not on r. -/
theorem producer_optimum_region_ii (P : Params) (hP : P.Standing) :
    (P.alpha < 1 / 2 → P.beta < P.od / 2 → ∀ d : Decision, d = ⟨1, 1, 1⟩ →
      DecisionFeasible P d ∧ OverPrescribes P d ∧
      (∀ (m : Model) (y : ℝ × ℝ) (d' : Decision), DecisionFeasible P d' → OverPrescribes P d' →
        producerProfit P m y d' ≤ producerProfit P m y d) ∧
      (∀ r t : ℝ, producerProfit P .EC (r, t) d = 1 - P.alpha - P.beta - P.k * r / 2) ∧
      (∀ r t : ℝ, producerProfit P .SR (r, t) d = 1 - P.alpha - P.beta - t)) ∧
    (P.alpha < 1 / 2 → P.od / 2 ≤ P.beta →
      ∀ d : Decision, d = ⟨1 - P.od + P.od ^ 2 / (2 * P.beta), 1, P.od / (2 * P.beta)⟩ →
      DecisionFeasible P d ∧ OverPrescribes P d ∧
      (∀ (m : Model) (y : ℝ × ℝ) (d' : Decision), DecisionFeasible P d' → OverPrescribes P d' →
        producerProfit P m y d' ≤ producerProfit P m y d) ∧
      (∀ r t : ℝ, producerProfit P .EC (r, t) d
        = (P.od ^ 2 - 2 * P.beta * (2 * P.alpha + P.k * r + 2 * (-1 + P.od))) / (4 * P.beta)) ∧
      (∀ r t : ℝ, producerProfit P .SR (r, t) d
        = (P.od ^ 2 + 4 * P.beta * (1 - P.alpha - P.od - t)) / (4 * P.beta))) ∧
    (1 / 2 ≤ P.alpha → P.beta < P.od / 2 →
      ∀ d : Decision, d = ⟨1 / (2 * P.alpha), 1 / (2 * P.alpha), 1⟩ →
      DecisionFeasible P d ∧ OverPrescribes P d ∧
      (∀ (m : Model) (y : ℝ × ℝ) (d' : Decision), DecisionFeasible P d' → OverPrescribes P d' →
        producerProfit P m y d' ≤ producerProfit P m y d) ∧
      (∀ r t : ℝ, producerProfit P .EC (r, t) d
        = (1 / 4) * (1 / P.alpha - 2 * (2 * P.beta + P.k * r))) ∧
      (∀ r t : ℝ, producerProfit P .SR (r, t) d
        = (1 - 4 * P.alpha * (P.beta + t)) / (4 * P.alpha))) ∧
    (1 / 2 ≤ P.alpha → P.od / 2 ≤ P.beta →
      ∀ d : Decision, d = ⟨(1 / 2) * (1 / P.alpha + P.od * (P.od - 2 * P.beta) / P.beta),
          1 / (2 * P.alpha), P.od / (2 * P.beta)⟩ →
      DecisionFeasible P d ∧ OverPrescribes P d ∧
      (∀ (m : Model) (y : ℝ × ℝ) (d' : Decision), DecisionFeasible P d' → OverPrescribes P d' →
        producerProfit P m y d' ≤ producerProfit P m y d) ∧
      (∀ r t : ℝ, producerProfit P .EC (r, t) d
        = (1 / 4) * (1 / P.alpha - 2 * P.k * r - 4 * P.od + P.od ^ 2 / P.beta)) ∧
      (∀ r t : ℝ, producerProfit P .SR (r, t) d
        = (1 / 4) * (1 / P.alpha + (P.od ^ 2 - 4 * P.beta * (P.od + t)) / P.beta))) := by sorry

end EPRPharma
