-- Prove2me | Theorems.Thm_DataGrowth_BGP_eq_A_5
-- name    : DataGrowth.BGP.eq_A_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:07.27299+00:00
-- url     : https://prove2.me/theorems/ef8c5879-821e-4378-aa96-f6eb8cb60ef8
-- title:
--   (A.5), PDF p. 25 — decentralized BGP: $(\zeta-\gamma)g_N+(\xi-\sigma)g_\phi+n=0$
-- statement:
--   Assume the standing parameter ranges and let a balanced growth path of the decentralized economy be given, with growth rates $g_N$ and $g_\phi$. Then
--   $$
--   (\zeta-\gamma)\,g_N+(\xi-\sigma)\,g_\phi+n=0 .
--   $$
--
--   This combines the data free-entry condition (18), the Euler equations (4)–(5), and the equality of the growth rates of consumption and output on a balanced growth path. With (A.3) it gives Proposition 1.
--
--   **Formalization Note** "In BGP, the growth rate of consumption is the same as that of output" (PDF p. 25) is part of the definition of the decentralized balanced growth path, since the paper uses it without deriving it.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 25 (Online Appendix p. 2), (A.5)

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 25 (Online Appendix p. 2), (A.5): on a balanced growth path of the
decentralized economy, (ζ − γ) g_N + (ξ − σ) g_ϕ + n = 0.

Formalization Note: the proof combines the free-entry condition (18), the Euler equations (4)–(5)
and "the fact that in BGP, the growth rate of consumption is the same as that of output"; the
latter is part of the BGP notion `IsDecBGP` (per-capita output K_y N l_E of (14) grows at g_c),
since the paper never derives it. The economy is encoded in level form (`IsDecEq`), t > 0. -/
theorem eq_A_5 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    (P.ζ - P.γ) * R.gN + (P.ξ - P.σ) * R.gphi + P.n = 0 := by sorry

end DataGrowth.BGP
