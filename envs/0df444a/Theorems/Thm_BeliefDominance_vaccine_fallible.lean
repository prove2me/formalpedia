-- Prove2me | Theorems.Thm_BeliefDominance_vaccine_fallible
-- name    : BeliefDominance.vaccine_fallible
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:00.12234+00:00
-- url     : https://prove2.me/theorems/ee048c2d-92b0-4347-b641-e33145b862c1
-- title:
--   §2 — the vaccine example of fallible inconsistency
-- statement:
--   In the vaccine problem, under belief dominance:
--
--   1. exactly seven strategies are nondominated, namely $(\alpha,\alpha,\beta)$, $(\alpha,\alpha,\gamma)$, $(\beta,\alpha,\beta)$, $(\beta,\alpha,\gamma)$, $(\gamma,\alpha,\beta)$, $(\gamma,\alpha,\gamma)$ and $(\gamma,\gamma,\gamma)$;
--   2. after the first-period action $\beta$ and strain $A$, the action $\beta$ is nondominated;
--   3. every strategy $(\beta,\beta,x_{2,B})$ is dominated in the first period;
--   4. the problem exhibits fallible inconsistency.
--
--   This is the paper's concrete witness that belief dominance, although weakly consistent, is not immune to fallible inconsistency: the nondominated strategy $(\beta,\alpha,\beta)$ supplies the first-period action of item 4.
--
--   Differences from the source:
--   - reading: Z ∈ {0,1}¹², and N(x, Y, Z) reads the strain Y; Table 1 fixes marginals and p.3 makes different vaccines independent → z = (s, b) with the strain s recorded in z and mass 0 on s ≠ y; under each belief the strain and all 12 entries of b are independent; reason: U(x₁, x₂, z) of §3 does not see y; every statement depends on the beliefs only through the marginals of Table 1
--   - reading: in the formula for fallible inconsistency x₁* is unbound → x₁* is the first-period action of some x* ∈ X*; reason: "despite the first-period action being optimal" and clause (a) of the proof of Theorem 4, p.11
--   - reading: ~_{x₁,y} and ≼_{x₁,y} are used on p.6 without a definition for belief dominance, and the generic ≺ of §3.2–3.3 is not spelled out → Indiff₂ is equality of V₂ on Φ_y, le₂ is Dominates₂ ∨ Indiff₂, and ≺ is strictPart; reason: analogy with the first-period definitions of p.5; le_isPreorder shows that dominance is exactly this strict part
--   - encoding: ∀ x̂₂(Y ≠ y) ∈ ∏_{ŷ≠y} X_{2,x₁*,ŷ} → ∀ s ∈ X with s.1 = x₁* and s.2 y = a; reason: the same completions, since a ∈ X_{2,x₁*,y}
--   - encoding: the iterated sum of (1) over 𝒴 and 𝒵 → one sum over Y × Z; reason: finite types, the two sums are equal
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, §2, p.4 and Figure 1; seven strategies, p.3

import Mathlib
import Definitions.Def_BeliefDominance_vaccineProblem

namespace BeliefDominance

/-- The vaccine example (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic Consistency*,
Management Science, doi:10.1287/mnsc.2020.3908, §2, pp.3–4 (PDF pp.4–5), Figure 1): seven strategies
are nondominated; after `(β, α, β)` and strain A, the action `β` is nondominated, although every
strategy `(β, β, x₂,B)` was dominated; so the problem exhibits fallible inconsistency. -/
theorem vaccine_fallible :
    optimalStrategies vaccineProblem.space vaccineProblem.le =
      {strat .α .α .β, strat .α .α .γ, strat .β .α .β, strat .β .α .γ,
        strat .γ .α .β, strat .γ .α .γ, strat .γ .γ .γ} ∧
    Vaccine.β ∈ optimalActions vaccineProblem.space vaccineProblem.le₂ .β .A ∧
    (∀ v : Vaccine, ∃ x ∈ vaccineProblem.space.strategies,
      vaccineProblem.Dominates x (strat .β .β v)) ∧
    ExhibitsFallible vaccineProblem.space vaccineProblem.le vaccineProblem.le₂ := by sorry

end BeliefDominance
