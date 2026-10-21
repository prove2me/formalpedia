-- Prove2me | Theorems.Thm_DataGrowth_BGP_eq_A_3
-- name    : DataGrowth.BGP.eq_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:56.370584+00:00
-- url     : https://prove2.me/theorems/8ec5fe90-1ea8-4055-a616-90d3046d0066
-- title:
--   (A.3), PDF p. 25 — decentralized BGP: $(\zeta-1)g_N+\xi g_\phi+n=0$
-- statement:
--   Assume the standing parameter ranges and let a balanced growth path of the decentralized economy be given, with growth rates $g_N=\dot N/N$ of the number of varieties and $g_\phi=\dot\phi/\phi$ of data per capita. Then
--   $$
--   (\zeta-1)\,g_N+\xi\,g_\phi+n=0 .
--   $$
--
--   This is the labor free-entry condition (19), combined with the wage (15) and (A.2), written in growth rates. Together with (A.5) it determines the two rates.
--
--   **Formalization Note** The economy is given by its level-form equilibrium conditions; the growth-form identities (A.1)–(A.2) are steps of the proof, not hypotheses.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 25 (Online Appendix p. 2), (A.3)

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 25 (Online Appendix p. 2), (A.3): on a balanced growth path of the
decentralized economy, (ζ − 1) g_N + ξ g_ϕ + n = 0, where g_N = Ṅ/N and g_ϕ = ϕ̇/ϕ.

Formalization Note: the economy is encoded by its level-form equilibrium conditions (`IsDecEq`:
(4), (5), (3) with s = 0, (9), (13), (15), (17)–(19), l_E + l_R = 1, t > 0); a BGP has each
variable at its own constant growth rate and r constant (`IsDecBGP`). The growth-form identities
(A.1)–(A.2) are steps of the proof, not hypotheses. -/
theorem eq_A_3 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    (P.ζ - 1) * R.gN + P.ξ * R.gphi + P.n = 0 := by sorry

end DataGrowth.BGP
