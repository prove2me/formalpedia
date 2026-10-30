-- Prove2me | Theorems.Thm_EPRPharma_producer_optimum_region_i
-- name    : EPRPharma.producer_optimum_region_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:22:38.236722+00:00
-- url     : https://prove2.me/theorems/904c91f9-9857-4c9f-92d0-3b6f2e8bb1ac
-- title:
--   The producer's best decision without over-prescription (region (i))
-- statement:
--   Assume the standing assumptions. Among the feasible decisions that do not induce over-prescription, the producer's profit is maximized, under either model and for every policy $(r,t)$, by
--
--   1. if $\alpha<1/4$: $p^*=1+u_p$, $\eta_d^*=1$, $\eta_p^*=0$, with
--   $$\Pi_m^{EC(i)*}(r)=\frac{3-6\alpha-kr+3u_p}{6},\qquad \Pi_m^{SR(i)*}(t)=\frac{1-2\alpha-t+u_p}{2};$$
--   2. if $\alpha\ge 1/4$: $p^*=\frac1{4\alpha}+u_p$, $\eta_d^*=\frac1{4\alpha}$, $\eta_p^*=0$, with
--   $$\Pi_m^{EC(i)*}(r)=\frac{3-8\alpha(kr-3u_p)}{48\alpha},\qquad \Pi_m^{SR(i)*}(t)=\frac{1-8\alpha(t-u_p)}{16\alpha}.$$
--
--   In each case the stated decision is feasible and does not induce over-prescription. This is the producer's best response if he keeps the doctor from over-prescribing; comparing it with region (ii) gives Propositions 1 and 2.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: region (i): p − u_p ≤ η_d < p + o_d(1 − η_p), 0 ≤ η_d, η_p ≤ 1 (App. p. 1) → the feasible decisions that do not induce over-prescription; reason: by Lemma 1 and the participation constraint for θ_n ∈ [0, 1] the two sets coincide
--   - generalization: Π^EC(·)*_m(r_EC) for r_EC ∈ [0,1] and Π^SR(·)*_m(t) for t ≥ 0 → the optimality and the profit formulas for every model and every real pair (r, t); reason: the optimum in a region does not depend on the policy and the profits are affine in r and t; the statement specializes to feasible policies
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), proof of Propositions 1–2, Region (i), Online Appendix p. 1 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_producerProfit
import Definitions.Def_EPRPharma_DecisionFeasible
import Definitions.Def_EPRPharma_OverPrescribes

namespace EPRPharma

/-- **The producer's optimum without over-prescription (region (i)).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), proof of Propositions 1–2, Online
Appendix p. 1 (unnumbered): "To satisfy p − u_p ≤ η_d < p + o_d (1 − η_p), we must have
p* = u_p + η*_d at the optimal solution. Then, we can identify the optimal solution by using
first-order conditions: if α < 1/4, we have p* = 1 + u_p, η*_d = 1, η*_p = 0, and
Π_m^EC(i)*(r_EC) = (3−6α−kr_EC+3u_p)/6 [Π_m^SR(i)*(t) = (1−2α−t+u_p)/2]; otherwise (i.e., if
α ≥ 1/4), we have p* = 1/(4α) + u_p, η*_d = 1/(4α), η*_p = 0, and Π_m^EC(i)*(r_EC) =
(3−8α (kr_EC−3u_p))/(48α) [Π_m^SR(i)*(t) = (1−8α (t−u_p))/(16α)]."

Under the standing assumptions, in each of the two cases the stated decision d₁ is feasible, does
not induce over-prescription, maximizes the producer's profit over all feasible decisions that do
not induce over-prescription (under either model and every policy), and earns the stated profit.

**Formalization Note.** Stated for every policy pair (r, t): the EC profit does not depend on t. -/
theorem producer_optimum_region_i (P : Params) (hP : P.Standing) :
    (P.alpha < 1 / 4 →
      DecisionFeasible P ⟨1 + P.up, 1, 0⟩ ∧ ¬ OverPrescribes P ⟨1 + P.up, 1, 0⟩ ∧
      (∀ (m : Model) (y : ℝ × ℝ) (d' : Decision), DecisionFeasible P d' → ¬ OverPrescribes P d' →
        producerProfit P m y d' ≤ producerProfit P m y ⟨1 + P.up, 1, 0⟩) ∧
      (∀ r t : ℝ, producerProfit P .EC (r, t) ⟨1 + P.up, 1, 0⟩
        = (3 - 6 * P.alpha - P.k * r + 3 * P.up) / 6) ∧
      (∀ r t : ℝ, producerProfit P .SR (r, t) ⟨1 + P.up, 1, 0⟩
        = (1 - 2 * P.alpha - t + P.up) / 2)) ∧
    (1 / 4 ≤ P.alpha →
      DecisionFeasible P ⟨1 / (4 * P.alpha) + P.up, 1 / (4 * P.alpha), 0⟩ ∧
      ¬ OverPrescribes P ⟨1 / (4 * P.alpha) + P.up, 1 / (4 * P.alpha), 0⟩ ∧
      (∀ (m : Model) (y : ℝ × ℝ) (d' : Decision), DecisionFeasible P d' → ¬ OverPrescribes P d' →
        producerProfit P m y d'
          ≤ producerProfit P m y ⟨1 / (4 * P.alpha) + P.up, 1 / (4 * P.alpha), 0⟩) ∧
      (∀ r t : ℝ, producerProfit P .EC (r, t) ⟨1 / (4 * P.alpha) + P.up, 1 / (4 * P.alpha), 0⟩
        = (3 - 8 * P.alpha * (P.k * r - 3 * P.up)) / (48 * P.alpha)) ∧
      (∀ r t : ℝ, producerProfit P .SR (r, t) ⟨1 / (4 * P.alpha) + P.up, 1 / (4 * P.alpha), 0⟩
        = (1 - 8 * P.alpha * (t - P.up)) / (16 * P.alpha))) := by sorry

end EPRPharma
