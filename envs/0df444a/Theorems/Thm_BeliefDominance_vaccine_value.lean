-- Prove2me | Theorems.Thm_BeliefDominance_vaccine_value
-- name    : BeliefDominance.vaccine_value
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:26:52.117343+00:00
-- url     : https://prove2.me/theorems/67a1a1ac-cdc9-4949-a93b-b81cbb639cab
-- title:
--   Appendix A — expected number of effective vaccines
-- statement:
--   In the vaccine problem the sums (1) exist, and for every strategy $x$ and virologist $i$,
--
--   $$
--   V(x,f_i)=\pi_i(A)\,E_i(A,x_1,x_{2,A})+\pi_i(B)\,E_i(B,x_1,x_{2,B}),
--   $$
--
--   where $E_i(s,v,v)=q_i(s,\text{two }v)$, and $E_i(s,v,v')=q_i(s,\text{one }v)+q_i(s,\text{one }v')$ for $v\ne v'$, with the entries of Table 1. In particular
--
--   $$
--   V((\beta,\alpha,\beta),f_1)=90\%\,(60\%+20\%)+10\%\cdot80\%=0.8.
--   $$
--
--   These are the values plotted in Figure 1, which decide every comparison of the example.
--
--   Differences from the source:
--   - reading: Z ∈ {0,1}¹², and N(x, Y, Z) reads the strain Y; Table 1 fixes marginals and p.3 makes different vaccines independent → z = (s, b) with the strain s recorded in z and mass 0 on s ≠ y; under each belief the strain and all 12 entries of b are independent; reason: U(x₁, x₂, z) of §3 does not see y; every statement depends on the beliefs only through the marginals of Table 1
--   - encoding: the iterated sum of (1) over 𝒴 and 𝒵 → one sum over Y × Z; reason: finite types, the two sums are equal
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, Appendix A, p.11

import Mathlib
import Definitions.Def_BeliefDominance_vaccineProblem

namespace BeliefDominance

/-- The expected number of effective vaccines (Ekholm–Baker, *Multiple Beliefs, Dominance and
Dynamic Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, Appendix A, p.11 (PDF p.12)):
the sums (1) exist, the value of a strategy is
`Pr(Y = A) E[N | Y = A] + Pr(Y = B) E[N | Y = B]`, and the strategy `(β, α, β)` has value `0.8` under
belief 1. -/
theorem vaccine_value :
    vaccineProblem.WellPosed ∧
    (∀ (x : Vaccine × (Strain → Vaccine)) (i : Virologist),
      vaccineProblem.V x (belief i) =
        strainProb i .A * conditionalValue i .A x.1 (x.2 .A) +
          strainProb i .B * conditionalValue i .B x.1 (x.2 .B)) ∧
    vaccineProblem.V (strat .β .α .β) (belief .v1) = 4 / 5 := by sorry

end BeliefDominance
