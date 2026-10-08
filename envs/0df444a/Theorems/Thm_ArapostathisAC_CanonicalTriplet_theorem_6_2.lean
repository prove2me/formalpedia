-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalTriplet_theorem_6_2
-- name    : ArapostathisAC.CanonicalTriplet.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:19:07.804061+00:00
-- url     : https://prove2.me/theorems/30e5c0b4-52cc-4b78-9a32-955e11d937c7
-- title:
--   Theorem 6.2 — $(\rho,h,\pi^*)$ is canonical iff $\rho,h$ solve the coupled optimality equations (6.6)–(6.7) with $\pi^*$ attaining both infima
-- statement:
--   Let $(\mathbf S,\mathbf A,U,P,c)$ be a controlled Markov process with Borel state space $\mathbf S$, Borel action space $\mathbf A$, nonempty compact admissible action sets $U(x)$ with measurable graph $\mathbf K$, transition kernel $P(dy\mid x,a)$, and a measurable one-stage cost $c\ge0$ that is bounded on $\mathbf K$ ($c\in\mathcal M_b(\mathbf K)$). Let $\pi^*\in\Pi_{SD}$ be a stationary deterministic policy and let $\rho,h\in\mathcal M_b(\mathbf S)$ be bounded measurable functions. Then $(\rho,h,\pi^*)$ is a canonical triplet, that is,
--   $$J_N(x,\pi^*,h)=J^*_N(x,h)=h(x)+N\rho(x)\qquad\forall N\in\mathbb N_0,\ x\in\mathbf S,$$
--   if and only if, for every $x\in\mathbf S$,
--   $$\rho(x)=\inf_{a\in U(x)}\Big\{\int_{\mathbf S}\rho(y)P(dy\mid x,a)\Big\}\tag{6.6}$$
--   $$\rho(x)+h(x)=\inf_{a\in U(x)}\Big\{c(x,a)+\int_{\mathbf S}h(y)P(dy\mid x,a)\Big\}\tag{6.7}$$
--   and $\pi^*(x)$ attains the infimum in both (6.6) and (6.7).
--
--   Here $J_N(x,\pi,h)=E^\pi_x[\sum_{t=0}^{N-1}c(X_t,A_t)+h(X_N)]$ and $J^*_N(x,h)$ is its infimum over all admissible (history-dependent, randomized) policies. (6.7) is the average cost optimality equation, and (6.6) lets the optimal average cost $\rho(\cdot)$ depend on the initial state, as in the multichain case. The theorem is due to Yushkevich; it is the bridge from the coupled optimality equations to strong average optimality of canonical policies (Theorem 6.3 of the paper).
--
--   **Formalization Note.** (6.6) and (6.7) together with "$\pi^*(x)$ attains the infimum" are stated in attained form: $\rho(x)=\int\rho\,dP(\cdot\mid x,\pi^*(x))$ and $\rho(x)\le\int\rho\,dP(\cdot\mid x,a)$ for all $a\in U(x)$, and likewise for (6.7); this is equivalent to the printed conditions and avoids the junk value of a real infimum. $\rho$ is a function, not a constant. $J^*_N$ is a real infimum over all admissible policies, which is the genuine infimum here because the family is bounded below by $-\sup|h|$ and nonempty ($\pi^*$ belongs to it). No continuity of $c$ or $P$ is assumed, as in the paper. The model's standing assumptions $c\ge0$ on $\mathbf K$ (Assumption 2.1) and compactness of $U(x)$ are part of the model.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 316–317, Theorem 6.2 ((6.4), (6.6), (6.7))

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP

open MeasureTheory ProbabilityTheory

namespace ArapostathisAC.CanonicalTriplet

theorem theorem_6_2 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (πstar : StationaryPolicy M)
    (ρ h : S → ℝ) (hρ : IsBoundedMeas ρ) (hh : IsBoundedMeas h) :
    IsCanonical M ρ h πstar.toPolicy ↔ (Eq66 M ρ πstar ∧ Eq67 M ρ h πstar) := by sorry

end ArapostathisAC.CanonicalTriplet
