-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalTriplet_sufficiency_lower
-- name    : ArapostathisAC.CanonicalTriplet.sufficiency_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:19:05.334733+00:00
-- url     : https://prove2.me/theorems/13d32fbc-bf64-4ccf-b4a1-e58f08ab0614
-- title:
--   Proof of Theorem 6.2, sufficiency — $J^*_{N+1}(x,h)\ge h(x)+(N+1)\rho(x)$
-- statement:
--   Let $(\mathbf S,\mathbf A,U,P,c)$ be a controlled Markov process with Borel state and action spaces and a cost $c\ge0$ that is bounded on $\mathbf K$. Let $\pi^*\in\Pi_{SD}$ and $\rho,h\in\mathcal M_b(\mathbf S)$ satisfy (6.6) and (6.7) with $\pi^*(x)$ attaining both infima:
--   $$\rho(x)=\inf_{a\in U(x)}\int_{\mathbf S}\rho(y)P(dy\mid x,a),\qquad \rho(x)+h(x)=\inf_{a\in U(x)}\Big\{c(x,a)+\int_{\mathbf S}h(y)P(dy\mid x,a)\Big\}.$$
--   Let $N\in\mathbb N_0$ and suppose that $J^*_N(y,h)=h(y)+N\rho(y)$ for all $y\in\mathbf S$. Then for every $x\in\mathbf S$,
--   $$J^*_{N+1}(x,h)\ge h(x)+(N+1)\rho(x).$$
--
--   This is the first display of the sufficiency part of the proof of Theorem 6.2 (the induction step for the lower bound), with the paper's step from $N-1$ to $N$ written as the step from $N$ to $N+1$.
--
--   **Formalization Note.** (6.6) and (6.7) are stated in attained form: equality at $a=\pi^*(x)$ and the inequality for every $a\in U(x)$, which is equivalent to "the infimum equals the left side and $\pi^*(x)$ attains it" and avoids real infima. $J^*_{N+1}$ is the infimum over all history-dependent randomized admissible policies.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 317, proof of Theorem 6.2, Sufficiency, first display

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP

open MeasureTheory ProbabilityTheory

namespace ArapostathisAC.CanonicalTriplet

theorem sufficiency_lower {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (πstar : StationaryPolicy M)
    (ρ h : S → ℝ) (hρ : IsBoundedMeas ρ) (hh : IsBoundedMeas h)
    (h66 : Eq66 M ρ πstar) (h67 : Eq67 M ρ h πstar) (N : ℕ)
    (hN : ∀ y, JNopt M N h y = h y + N * ρ y) :
    ∀ x, h x + ((N : ℝ) + 1) * ρ x ≤ JNopt M (N + 1) h x := by sorry

end ArapostathisAC.CanonicalTriplet
