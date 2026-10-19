-- Prove2me | Theorems.Thm_DataGrowth_BGP_proposition_1
-- name    : DataGrowth.BGP.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:56.933987+00:00
-- url     : https://prove2.me/theorems/56e805f0-a549-4c82-8c75-57b3f0109342
-- title:
--   Proposition 1, p. 9 — decentralized BGP growth rates (20)–(21); the data constraint never binds
-- statement:
--   Assume the standing parameter ranges and let a balanced growth path of the decentralized economy be given, with growth rates $g_c,g_N,g_\phi$ of consumption, varieties and data per capita. Write $D=(1-\zeta)\sigma-\xi(1-\gamma)$. Then
--   $$
--   g_c=g_N=g^*=\frac{\sigma}{D}\,n,\qquad g_\phi=g^*_\phi=\frac{1-\gamma}{D}\,n,
--   $$
--   the data constraint (3) never binds, i.e. $g_\phi<g_c$, and if $\gamma>1$ then $g_\phi<0$.
--
--   The rates depend neither on the population level $L_0$ nor on $\eta,\beta,\psi,\rho$: growth has no scale effect. Data per capita shrink on the balanced growth path when $\gamma>1$, while aggregate data use may grow.
--
--   **Formalization Note** $g^*_y=g^*_c$ holds by the definition of the balanced growth path. With $s=0$, (3) reads $\dot\phi/\phi\le\dot c/c$, so "never binds" is the strict inequality. The sign $g^*_\phi<0$ in (21) holds only for $\gamma>1$ (for $0<\gamma<1$ it is positive; p. 10 says "In general, when $\gamma>1$"), so it is stated under that hypothesis.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 9, Proposition 1, (20)–(21)

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, p. 9, Proposition 1: on a balanced growth path of the decentralized economy the
growth rates are (20) g*_c = g*_y = g*_N = g* = σn/((1 − ζ)σ − ξ(1 − γ)) and (21)
g*_ϕ = (1 − γ)n/((1 − ζ)σ − ξ(1 − γ)); the data constraint (3) never binds; and g*_ϕ < 0.

Formalization Note:
* g*_y = g*_c holds by the definition `IsDecBGP` (per-capita output grows at g_c), so it is not
  restated.
* With s = 0 the constraint (3) is ϕ̇/ϕ ≤ ċ/c; "never binds under BGP" is the strict inequality
  g_ϕ < g_c.
* The sign g*_ϕ < 0 of (21) holds only when γ > 1 (for 0 < γ < 1 inside Proposition A.1's range
  g*_ϕ > 0; p. 10 says "In general, when γ > 1"), so it is stated under 1 < γ.
* "Does not exhibit scale effect" is visible in the formulas: the rates do not depend on L(0).
* The economy is encoded by its level-form equilibrium conditions (`IsDecEq`) on t > 0, with
  s = 0, θ = 0 and l_E + l_R = 1. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    R.gc = P.gStar ∧ R.gN = P.gStar ∧ R.gphi = P.gPhiStar ∧ R.gphi < R.gc ∧
      (1 < P.γ → R.gphi < 0) := by sorry

end DataGrowth.BGP
