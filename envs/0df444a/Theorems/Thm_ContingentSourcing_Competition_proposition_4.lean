-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_proposition_4
-- name    : ContingentSourcing.Competition.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:03.673456+00:00
-- url     : https://prove2.me/theorems/de65de96-701b-4529-8c48-661b3e3d36ca
-- title:
--   Proposition 4(i)–(iii), pp. 21–22 — for c_R > ψ_2, contingent sourcing makes both suppliers weakly better off and the buyer better or worse off by threshold
-- statement:
--   Compare the pricing game with perfect shipment information ($\rho=1$, contingent sourcing possible) and without it ($\rho=0$). For an equilibrium $w^I$ at $\rho=1$ and an equilibrium $w^N$ at $\rho=0$, write $\pi_U,\pi_R$ for the suppliers' payoffs (5)–(6) and $\pi_B$ for the buyer's optimal expected profit in (2). Let
--   $$t=m-\frac{P_1m-c_U}{\sqrt{4-P_1+P_1^2}},\qquad \psi_2=\frac{P_0m+2c_U/P_1}{P_0+2},\qquad \phi_1=\frac{(1+P_0)m+c_U}{2}.$$
--
--   If $c_R>\psi_2$, equilibria exist at both $\rho=1$ and $\rho=0$. Moreover, for every equilibrium $w^I$ at $\rho=1$ and every equilibrium $w^N$ at $\rho=0$:
--
--   1. if $c_R\ge\phi_1$: $\pi_U(w^I)=\pi_U(w^N)$, $\pi_B(w^I)\ge\pi_B(w^N)$, $\pi_R(w^I)\ge\pi_R(w^N)$, and both inequalities are strict when $c_R<m$;
--   2. if $t<c_R<\phi_1$: the buyer, supplier U and supplier R are all strictly better off at $w^I$;
--   3. if $\psi_2<c_R\le t$: the buyer is weakly worse off at $w^I$ (strictly when $c_R<t$), and both suppliers are strictly better off.
--
--   The possibility of contingent sourcing thus always benefits the suppliers in this range, while it can make the buyer worse off by softening the price competition between the suppliers.
--
--   **Formalization Note.** The strict claims are weakened at three endpoints where the printed strict claims fail: at $c_R=m$ the emergency order is $0$ and the buyer and R tie; at $c_R=\phi_1$ U's payoff is unaffected, which case 1 covers; at $c_R=t$ the buyer ties. Part (iv) of the paper ("otherwise … no impact") is not stated: it is false as printed (at $m=10$, $P_1=1/2$, $c_U=0$, $c_R=3/2<\psi_2=2$ there is an undominated contingent-sourcing equilibrium at $\rho=1$ with payoffs different from the unique $\rho=0$ equilibrium). An equilibrium is a Pareto-dominant (undominated) Nash equilibrium. The buyer's payoff is the supremum of (2) over feasible orders.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, pp. 21–22 (PDF 21–22), Proposition 4(i)–(iii)

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Proposition 4(i)–(iii), pp. 21–22: comparison of every equilibrium with perfect shipment
information (ρ = 1) against every equilibrium without it (ρ = 0), for c_R > ψ_2. -/
theorem proposition_4 (P : Params) (hP : P.Standing) :
    (P.psi2 < P.cR → (∃ w, P.IsEquilibrium 1 w) ∧ (∃ w, P.IsEquilibrium 0 w)) ∧
    ∀ wI wN : Prices, P.IsEquilibrium 1 wI → P.IsEquilibrium 0 wN →
      (P.phi1 ≤ P.cR →
        P.payU 1 wI = P.payU 0 wN ∧ P.buyerValue 0 wN ≤ P.buyerValue 1 wI ∧
        P.payR 0 wN ≤ P.payR 1 wI ∧
        (P.cR < P.m → P.buyerValue 0 wN < P.buyerValue 1 wI ∧ P.payR 0 wN < P.payR 1 wI)) ∧
      (P.buyerThreshold < P.cR → P.cR < P.phi1 →
        P.buyerValue 0 wN < P.buyerValue 1 wI ∧ P.payU 0 wN < P.payU 1 wI ∧
        P.payR 0 wN < P.payR 1 wI) ∧
      (P.psi2 < P.cR → P.cR ≤ P.buyerThreshold →
        P.buyerValue 1 wI ≤ P.buyerValue 0 wN ∧
        (P.cR < P.buyerThreshold → P.buyerValue 1 wI < P.buyerValue 0 wN) ∧
        P.payU 0 wN < P.payU 1 wI ∧ P.payR 0 wN < P.payR 1 wI) := by sorry

end ContingentSourcing.Competition
