-- Prove2me | Theorems.Thm_EPRPharma_proposition_4_welfare_maximizing_model
-- name    : EPRPharma.proposition_4_welfare_maximizing_model
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:27:25.282805+00:00
-- url     : https://prove2.me/theorems/7076388c-ddd4-45d4-b8ca-fdb125044440
-- title:
--   Proposition 4 (Table 2): health-benefit, collection-cost and environmental-disutility thresholds determine whether EC or SR maximizes total welfare
-- statement:
--   There exist thresholds $\bar u_p^{EC},\bar u_p^{SR}$ (functions of $\alpha,\beta,o_d$), $\bar k$ (a function of $\alpha,\beta,o_d,u_p$) and $\bar\epsilon_e^{EC},\tilde\epsilon_e$ (functions of $\alpha,\beta,o_d,u_p,k,\epsilon_s$) such that, under the standing assumptions, the following hold.
--
--   1. *(Proposition 1)* If $u_p<\bar u_p^{EC}$, then at every feasible EC policy with nonnegative optimal producer profit, inducing over-prescription is strictly more profitable; the same holds under SR when $u_p<\bar u_p^{SR}$; and $\bar u_p^{EC}<\bar u_p^{SR}$.
--   2. *(Proposition 2)* If $u_p\ge\bar u_p^{EC}$ and $k<\bar k$, inducing over-prescription is strictly more profitable at every feasible EC policy.
--   3. *(p. 17)* Over-prescription can be eliminated under EC if and only if $u_p\ge\bar u_p^{EC}$ and $k\ge\bar k$, and under SR if and only if $u_p\ge\bar u_p^{SR}$.
--   4. *(Proposition 3)* If $u_p\ge\bar u_p^{EC}$ and $k\ge\bar k$, eliminating over-prescription is total welfare maximizing under EC if and only if $\epsilon_e\ge\bar\epsilon_e^{EC}$; $\bar\epsilon_e^{EC}$ is nonincreasing in $\epsilon_s$; and $\tilde\epsilon_e\ge\bar\epsilon_e^{EC}$.
--   5. *(Table 2)* The total welfare maximizing model is
--
--   | | $u_p<\bar u_p^{EC}$ | $\bar u_p^{EC}\le u_p<\bar u_p^{SR}$ | $u_p\ge\bar u_p^{SR}$ |
--   |---|---|---|---|
--   | $k<\bar k$ | EC = SR | EC = SR | SR |
--   | $k\ge\bar k$ | EC = SR | EC if $\epsilon_e\ge\tilde\epsilon_e$, SR otherwise | EC if $\epsilon_e\ge\tilde\epsilon_e$, SR otherwise |
--
--   where "EC = SR" means that the maximal total welfare of the two models is equal, "SR" that SR's maximal welfare is at least EC's, and "EC" that EC's is at least SR's.
--
--   The proposition says that the model with two levers (SR) is not always better: when over-prescription can be eliminated through the collection obligation and the environmental damage is high, End-of-pipe Control is at least as good; when the medicine's health benefit is low, the two models are equivalent.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: the planner maximizes W(y_P) subject to 0 ≤ r_P ≤ 1, t ≥ 0, Π*_m ≥ 0, Π_sp ≥ 0, anticipating the producer's optimal decision (pp. 11, 13) → IsEquilibrium: a feasible policy y with an optimal producer decision d, Π_m ≥ 0 and Π_sp ≥ 0; the planner may select among the producer's tied optimal decisions; reason: at r̄_EC and t̄ the producer is indifferent and the proof (App. p. 2) assigns r̄_EC to both regions; no uniqueness of the producer's response is assumed
--   - reading: Table 2 entries 'EC = SR', 'SR', 'EC when ε_e ≥ ε̃_e, SR otherwise' (p. 18) → attained maximal welfare over equilibria: equal maxima; W*_SR ≥ W*_EC; W*_EC ≥ W*_SR when ε_e ≥ ε̃ and W*_SR ≥ W*_EC when ε_e < ε̃; reason: p. 19 'the SR model weakly dominates', App. p. 5 'at least as high'; attainment is asserted, which is stronger than a comparison of suprema
--   - reading: thresholds with suppressed arguments, ū_p^EC, ū_p^SR, k̄(u_p), ε̄_e(u_p,k), ε̃_e(u_p,k) (p. 15) → ū^EC, ū^SR functions of (α, β, o_d); k̄ of (α, β, o_d, u_p); ε̄^EC, ε̄^SR, ε̃ of (α, β, o_d, u_p, k, ε_s); reason: the paper writes k̄(u_p) and ε̄(u_p,k) and differentiates ε̄ in ε_s; no threshold depends on the variable it thresholds
--   - reading: thresholds 'as presented in Propositions 1, 2, 3' (p. 17) → the thresholds satisfy the printed properties of Propositions 1–3 and the p. 17 identification: over-prescription can be eliminated under EC iff u_p ≥ ū^EC and k ≥ k̄, under SR iff u_p ≥ ū^SR; reason: p. 17: 'the cases where over-prescription can be eliminated (i.e., u_p ≥ ū_p^EC and k ≥ k̄ under the EC model and u_p ≥ ū_p^SR under the SR model)'; without it ū = −1 and k̄ = 0 satisfy Propositions 1–2
--   - generalization: the proofs treat α < 1/4 and β < o_d/2 with r^i_EC, r^ii_EC ≥ 0 (App. pp. 2–5) → every α > 0 and β > 0; reason: the printed propositions carry no restriction on α, β and App. p. 1 gives the producer's optimum in all four (α, β) cases; the statement specializes to the paper's case
--   - reading: no sign conditions printed on α, β, o_d, u_p, k, ε_e, ε_s → α, β, o_d, k > 0 and u_p, ε_e, ε_s ≥ 0 (Params.Standing); reason: α, β are quadratic cost constants and the proofs divide by α, β, k; u_p ≥ 0 is used in the proof of Lemma 1; ε_e ≥ 0 is necessary (α = β = o_d = 1: no equilibrium over-prescribes, so 'iff ε_e ≥ ε̄' has no real threshold on all of ℝ)
--   - encoding: an EC policy is r_EC; an SR policy is (r_SR, t) → a policy is a pair (r, t); an EC policy is (r_EC, 0); reason: no EC quantity reads t, so the instances are the same
--   - reading: over-prescription: 'prescription medicine beyond the need of the patient (q_p > θ_n)' (p. 10) → OverPrescribes: q*_p(θ_n) > θ_n for some θ_n ∈ [0, 1]; reason: the decision is fixed before θ_n is drawn; by Lemma 1 this is η_d ≥ p + o_d(1 − η_p)
--   - reading: 'the producer gains a higher profit by inducing over-prescription' → some feasible decision inducing over-prescription earns strictly more than every feasible decision that does not; reason: the comparison of the producer's best profits in the two regions (App. p. 2: Π^EC(ii)* > Π^EC(i)*), with the region-(ii) best attained
--   - reading: 'r_EC (t) that maintains a non-negative producer profit' → the producer has an optimal decision at (m, y) and its profit is ≥ 0; reason: App. p. 2: 'for any r_EC [t] that maintains a non-negative producer profit, i.e., for any r_EC ≤ r^ii_EC [t ≤ t^ii]', the optimal profit Π*_m ≥ 0
--   - reading: 'it is total welfare maximizing to eliminate over-prescription' → some equilibrium without over-prescription attains the maximal welfare over all equilibria of the model; reason: App. pp. 2–3 compare W^EC(i)* with W^EC(ii)*; at equality both are maximizing
--   - reading: ∂ε̄_e^EC/∂ε_s ≤ 0 (Proposition 3, p. 17) → ε̄^EC is antitone in ε_s; reason: the paper's threshold is piecewise with kinks (App. pp. 2–3); antitone is the derivative condition without differentiability
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Proposition 4, p. 17; Table 2, p. 18; proof, Online Appendix pp. 3–5

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_PolicyFeasible
import Definitions.Def_EPRPharma_NonnegOptimalProfit
import Definitions.Def_EPRPharma_OPStrictlyMoreProfitable
import Definitions.Def_EPRPharma_CanEliminate
import Definitions.Def_EPRPharma_EliminationOptimal
import Definitions.Def_EPRPharma_WelfareEqual
import Definitions.Def_EPRPharma_WelfareAtLeast

namespace EPRPharma

/-- **Proposition 4 (Table 2): thresholds in u_p, k and ε_e decide which EPR model maximizes total
welfare.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Proposition 4, p. 17:
"There exist unit health benefit thresholds ū_p^EC, ū_p^SR (as presented in Proposition 1), a unit
collection cost threshold k̄(u_p) (as presented in Proposition 2) for u_p ≥ ū_p^EC, and a unit
environmental disutility threshold ε̃_e(u_p,k) ≥ ε̄_e^EC(u_p,k) (as presented in Proposition 3) that
collectively determine the total welfare maximizing EPR implementation model as shown in Table 2."
Table 2, p. 18, "Total Welfare Maximizing EPR Implementation Model for Pharmaceuticals": columns
u_p < ū_p^EC | ū_p^EC ≤ u_p < ū_p^SR | u_p ≥ ū_p^SR; row k < k̄: EC = SR | EC = SR | SR; row k ≥ k̄:
(EC = SR, the first column spans both rows) | "EC when ε_e ≥ ε̃_e, SR otherwise" (spanning the
second and third columns).

There are functions ū^EC, ū^SR of (α, β, o_d), k̄ of (α, β, o_d, u_p) and ε̄^EC, ε̃ of
(α, β, o_d, u_p, k, ε_s) such that, under the standing assumptions:
1. (Proposition 1) if u_p < ū^EC, over-prescription is strictly more profitable at every feasible EC
   policy with nonnegative optimal producer profit; the same under SR with ū^SR; and ū^EC < ū^SR;
2. (Proposition 2) if u_p ≥ ū^EC and k < k̄, over-prescription is strictly more profitable at every
   feasible EC policy;
3. (p. 17) over-prescription can be eliminated under EC iff u_p ≥ ū^EC and k ≥ k̄, and under SR iff
   u_p ≥ ū^SR;
4. (Proposition 3) if u_p ≥ ū^EC and k ≥ k̄, eliminating over-prescription is total welfare
   maximizing under EC iff ε_e ≥ ε̄^EC; ε̄^EC is nonincreasing in ε_s; and ε̃ ≥ ε̄^EC there;
5. (Table 2) if u_p < ū^EC the two models give equal maximal welfare; if ū^EC ≤ u_p < ū^SR and
   k < k̄, equal maximal welfare; if u_p ≥ ū^SR and k < k̄, SR's maximal welfare is at least EC's;
   if u_p ≥ ū^EC and k ≥ k̄, EC's maximal welfare is at least SR's when ε_e ≥ ε̃ and SR's is at
   least EC's otherwise.

**Formalization Note.** "As presented in Propositions 1–3" is read as: the thresholds satisfy the
printed properties of Propositions 1–3 together with the p. 17 identification of the cases where
over-prescription can be eliminated (clause 3), which pins ū^EC, ū^SR, k̄ and ε̄^EC; Proposition 3's
∂ε̄_e^EC/∂ε_s ≤ 0 is read as: ε̄^EC is antitone in ε_s. Table 2's
entries compare attained maximal welfare over equilibria (the planner may select among the
producer's tied optimal decisions). The statement covers every α, β > 0; the paper's proofs treat
α < 1/4, β < o_d/2 with nonnegative region profits. -/
theorem proposition_4_welfare_maximizing_model :
    ∃ (uEC uSR : ℝ → ℝ → ℝ → ℝ) (kbar : ℝ → ℝ → ℝ → ℝ → ℝ)
      (epsBarEC epsTilde : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ),
      -- Proposition 1
      (∀ P : Params, P.Standing → P.up < uEC P.alpha P.beta P.od →
        ∀ y : ℝ × ℝ, PolicyFeasible .EC y → NonnegOptimalProfit P .EC y →
          OPStrictlyMoreProfitable P .EC y) ∧
      (∀ P : Params, P.Standing → P.up < uSR P.alpha P.beta P.od →
        ∀ y : ℝ × ℝ, PolicyFeasible .SR y → NonnegOptimalProfit P .SR y →
          OPStrictlyMoreProfitable P .SR y) ∧
      (∀ a b o : ℝ, 0 < a → 0 < b → 0 < o → uEC a b o < uSR a b o) ∧
      -- Proposition 2
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        P.k < kbar P.alpha P.beta P.od P.up →
        ∀ y : ℝ × ℝ, PolicyFeasible .EC y → OPStrictlyMoreProfitable P .EC y) ∧
      -- p. 17: when over-prescription can be eliminated
      (∀ P : Params, P.Standing →
        (CanEliminate P .EC ↔
          uEC P.alpha P.beta P.od ≤ P.up ∧ kbar P.alpha P.beta P.od P.up ≤ P.k)) ∧
      (∀ P : Params, P.Standing → (CanEliminate P .SR ↔ uSR P.alpha P.beta P.od ≤ P.up)) ∧
      -- Proposition 3 (EC), and ε̃_e ≥ ε̄_e^EC
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        (EliminationOptimal P .EC ↔
          epsBarEC P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE)) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        ∀ s' : ℝ, P.epsS ≤ s' →
          epsBarEC P.alpha P.beta P.od P.up P.k s'
            ≤ epsBarEC P.alpha P.beta P.od P.up P.k P.epsS) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        epsBarEC P.alpha P.beta P.od P.up P.k P.epsS
          ≤ epsTilde P.alpha P.beta P.od P.up P.k P.epsS) ∧
      -- Table 2
      (∀ P : Params, P.Standing → P.up < uEC P.alpha P.beta P.od → WelfareEqual P) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        P.up < uSR P.alpha P.beta P.od → P.k < kbar P.alpha P.beta P.od P.up →
        WelfareEqual P) ∧
      (∀ P : Params, P.Standing → uSR P.alpha P.beta P.od ≤ P.up →
        P.k < kbar P.alpha P.beta P.od P.up → WelfareAtLeast P .SR .EC) ∧
      (∀ P : Params, P.Standing → uEC P.alpha P.beta P.od ≤ P.up →
        kbar P.alpha P.beta P.od P.up ≤ P.k →
        (epsTilde P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE → WelfareAtLeast P .EC .SR) ∧
        (P.epsE < epsTilde P.alpha P.beta P.od P.up P.k P.epsS → WelfareAtLeast P .SR .EC)) := by sorry

end EPRPharma
