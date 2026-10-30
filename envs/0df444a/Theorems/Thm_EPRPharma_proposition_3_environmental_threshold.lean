-- Prove2me | Theorems.Thm_EPRPharma_proposition_3_environmental_threshold
-- name    : EPRPharma.proposition_3_environmental_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:46.514217+00:00
-- url     : https://prove2.me/theorems/29a3f6b5-0981-4b67-979d-c2d920038752
-- title:
--   Proposition 3: environmental disutility thresholds $\bar\epsilon_e^{EC}$, $\bar\epsilon_e^{SR}$ for eliminating over-prescription
-- statement:
--   There exist environmental disutility thresholds $\bar\epsilon_e^{EC}$ and $\bar\epsilon_e^{SR}$, functions of $(\alpha,\beta,o_d,u_p,k,\epsilon_s)$, such that, under the standing assumptions, for each model $P\in\{EC,SR\}$ under which over-prescription can be eliminated (that is, $u_p\ge\bar u_p^{EC}$ and $k\ge\bar k$ under EC, $u_p\ge\bar u_p^{SR}$ under SR):
--
--   1. it is total welfare maximizing to eliminate over-prescription under $P$ if and only if
--   $$\epsilon_e\ \ge\ \bar\epsilon_e^{P}(\alpha,\beta,o_d,u_p,k,\epsilon_s);$$
--   2. the threshold $\bar\epsilon_e^{P}$ is nonincreasing in the unit social disutility $\epsilon_s$ (the paper's $\partial\bar\epsilon_e^{P}/\partial\epsilon_s\le 0$).
--
--   Eliminating over-prescription lowers the environmental and social damage but costs the producer and the doctor; it pays exactly when the environmental damage of the medicine is high enough, and less environmental damage is needed when the social damage of unused medicine is higher.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - encoding: expectations over θ_n ~ U[0,1] and θ_u ~ U[0,1] independent of θ_n (pp. 8, 11) → interval integrals over [0, 1] (E1) and iterated interval integrals over [0, 1]² (E2); reason: the same distribution; every integrand is bounded and piecewise affine on [0, 1]
--   - reading: the producer's constraint U_d(q*_p) ≥ 0 (p. 11), price p unconstrained → U_d(q*_p(θ_n)) ≥ 0 for every θ_n ∈ [0, 1], p ∈ ℝ; reason: p. 15: 'we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0'; App. p. 1: 'we may have p* < 0'
--   - reading: the planner maximizes W(y_P) subject to 0 ≤ r_P ≤ 1, t ≥ 0, Π*_m ≥ 0, Π_sp ≥ 0, anticipating the producer's optimal decision (pp. 11, 13) → IsEquilibrium: a feasible policy y with an optimal producer decision d, Π_m ≥ 0 and Π_sp ≥ 0; the planner may select among the producer's tied optimal decisions; reason: at r̄_EC and t̄ the producer is indifferent and the proof (App. p. 2) assigns r̄_EC to both regions; no uniqueness of the producer's response is assumed
--   - reading: thresholds with suppressed arguments, ū_p^EC, ū_p^SR, k̄(u_p), ε̄_e(u_p,k), ε̃_e(u_p,k) (p. 15) → ū^EC, ū^SR functions of (α, β, o_d); k̄ of (α, β, o_d, u_p); ε̄^EC, ε̄^SR, ε̃ of (α, β, o_d, u_p, k, ε_s); reason: the paper writes k̄(u_p) and ε̄(u_p,k) and differentiates ε̄ in ε_s; no threshold depends on the variable it thresholds
--   - generalization: the proofs treat α < 1/4 and β < o_d/2 with r^i_EC, r^ii_EC ≥ 0 (App. pp. 2–5) → every α > 0 and β > 0; reason: the printed propositions carry no restriction on α, β and App. p. 1 gives the producer's optimum in all four (α, β) cases; the statement specializes to the paper's case
--   - reading: no sign conditions printed on α, β, o_d, u_p, k, ε_e, ε_s → α, β, o_d, k > 0 and u_p, ε_e, ε_s ≥ 0 (Params.Standing); reason: α, β are quadratic cost constants and the proofs divide by α, β, k; u_p ≥ 0 is used in the proof of Lemma 1; ε_e ≥ 0 is necessary (α = β = o_d = 1: no equilibrium over-prescribes, so 'iff ε_e ≥ ε̄' has no real threshold on all of ℝ)
--   - reading: ∂ε̄_e^EC/∂ε_s ≤ 0 (∂ε̄_e^SR/∂ε_s ≤ 0) → ε̄^EC and ε̄^SR are antitone in ε_s; reason: the paper's threshold is piecewise with kinks (App. pp. 2–3); antitone is the derivative condition without differentiability
--   - encoding: an EC policy is r_EC; an SR policy is (r_SR, t) → a policy is a pair (r, t); an EC policy is (r_EC, 0); reason: no EC quantity reads t, so the instances are the same
--   - reading: over-prescription: 'prescription medicine beyond the need of the patient (q_p > θ_n)' (p. 10) → OverPrescribes: q*_p(θ_n) > θ_n for some θ_n ∈ [0, 1]; reason: the decision is fixed before θ_n is drawn; by Lemma 1 this is η_d ≥ p + o_d(1 − η_p)
--   - reading: the hypothesis 'u_p ≥ ū_p^EC and k ≥ k̄ under EC (u_p ≥ ū_p^SR under SR)' → over-prescription can be eliminated under EC (SR), i.e. some equilibrium of the model has no over-prescription; reason: p. 17 identifies these cases ('i.e.'); this keeps the item from referring to another item's existential thresholds
--   - reading: 'it is total welfare maximizing to eliminate over-prescription' → some equilibrium without over-prescription attains the maximal welfare over all equilibria of the model; reason: App. pp. 2–3 compare W^EC(i)* with W^EC(ii)*; at equality both are maximizing
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Proposition 3, p. 17; proof, Online Appendix pp. 2–3

import Mathlib
import Definitions.Def_EPRPharma_Params_Standing
import Definitions.Def_EPRPharma_CanEliminate
import Definitions.Def_EPRPharma_EliminationOptimal

namespace EPRPharma

/-- **Proposition 3: an environmental disutility threshold above which eliminating
over-prescription is welfare maximizing, nonincreasing in ε_s.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Proposition 3, p. 17:
"Suppose u_p ≥ ū_p^EC and k ≥ k̄ under the EC model (u_p ≥ ū_p^SR under the SR model). There exists
an environmental disutility threshold ε̄_e^EC(u_p,k) (ε̄_e^SR(u_p,k)) such that it is total welfare
maximizing to eliminate over-prescription if and only if ε_e ≥ ε̄_e^EC (ε_e ≥ ε̄_e^SR).
Furthermore, we have ∂ε̄_e^EC/∂ε_s ≤ 0 (∂ε̄_e^SR/∂ε_s ≤ 0)."

There are functions ε̄^EC, ε̄^SR of (α, β, o_d, u_p, k, ε_s) such that, under the standing
assumptions, for each model m ∈ {EC, SR} in which over-prescription can be eliminated: it is total
welfare maximizing to eliminate over-prescription under m iff ε_e ≥ ε̄^m, and ε̄^m is nonincreasing
in ε_s.

**Formalization Note.** The hypothesis "u_p ≥ ū_p^EC and k ≥ k̄" ("u_p ≥ ū_p^SR") is written as
"over-prescription can be eliminated under EC (SR)", by the p. 17 "i.e." ("the cases where
over-prescription can be eliminated (i.e., u_p ≥ ū_p^EC and k ≥ k̄ under the EC model and
u_p ≥ ū_p^SR under the SR model)"). The derivative condition is read as: the threshold is antitone
in ε_s. The threshold sees ε_s as an argument (it is differentiated in ε_s) but not ε_e. -/
theorem proposition_3_environmental_threshold :
    ∃ epsBarEC epsBarSR : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
      ∀ P : Params, P.Standing →
        (CanEliminate P .EC →
          (EliminationOptimal P .EC ↔
              epsBarEC P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE) ∧
            ∀ s' : ℝ, P.epsS ≤ s' →
              epsBarEC P.alpha P.beta P.od P.up P.k s'
                ≤ epsBarEC P.alpha P.beta P.od P.up P.k P.epsS) ∧
        (CanEliminate P .SR →
          (EliminationOptimal P .SR ↔
              epsBarSR P.alpha P.beta P.od P.up P.k P.epsS ≤ P.epsE) ∧
            ∀ s' : ℝ, P.epsS ≤ s' →
              epsBarSR P.alpha P.beta P.od P.up P.k s'
                ≤ epsBarSR P.alpha P.beta P.od P.up P.k P.epsS) := by sorry

end EPRPharma
