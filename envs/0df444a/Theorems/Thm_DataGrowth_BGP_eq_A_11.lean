-- Prove2me | Theorems.Thm_DataGrowth_BGP_eq_A_11
-- name    : DataGrowth.BGP.eq_A_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:16.383995+00:00
-- url     : https://prove2.me/theorems/bab18c00-b22f-4f1c-9e35-dc4b0b8cb9c4
-- title:
--   (A.11), PDF p. 27 — planner BGP: $g_c=\frac1\gamma(g_N-\sigma g_\phi)$
-- statement:
--   Assume the standing parameter ranges and let a balanced growth path of the planner's necessary-condition system be given, with growth rates $g_c,g_N,g_\phi$. Then
--   $$
--   g_c=\frac{1}{\gamma}\big(g_N-\sigma g_\phi\big).
--   $$
--
--   It follows from the conditions (A.7)–(A.9) on consumption, data and labor written in growth rates, using that the labor shares are constant (Lemma A.1). It is the first of the two relations that pin down the planner's growth rates.
--
--   **Formalization Note** The planner's economy is its Hamiltonian necessary-condition system; the optimal control problem (24) is not formalized.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 27 (Online Appendix p. 4), (A.11)

import Mathlib
import Definitions.Def_DataGrowth_BGP_Planner

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 27 (Online Appendix p. 4), (A.11): on a balanced growth path of the
planner's necessary-condition system, ċ/c = g* = (1/γ)(Ṅ/N − σ ϕ̇/ϕ).

Formalization Note: the planner's economy is encoded by the current-value Hamiltonian's necessary
conditions (25)–(27), (A.7)–(A.10) (`IsPlanEq`); the optimal control problem (24) is not
formalized, and the planner's BGP is a BGP of this system (`IsPlanBGP`, each variable at its own
constant growth rate, t > 0). The proof uses that l_R is constant (footnote 13, Lemma A.1). -/
theorem eq_A_11 (P : Params) (hP : P.Standing) (S : PlanPath) (Q : PlanRates)
    (hS : IsPlanBGP P S Q) :
    Q.gc = (1 / P.γ) * (Q.gN - P.σ * Q.gphi) := by sorry

end DataGrowth.BGP
