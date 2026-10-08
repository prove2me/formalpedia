-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalTriplet_sufficiency_upper
-- name    : ArapostathisAC.CanonicalTriplet.sufficiency_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:18:38.457224+00:00
-- url     : https://prove2.me/theorems/9fbce855-e2f6-425b-a4cb-90cba746fd65
-- title:
--   Proof of Theorem 6.2, sufficiency — $J_{N+1}(x,\pi^*,h)=h(x)+(N+1)\rho(x)\ge J^*_{N+1}(x,h)$
-- statement:
--   Let $(\mathbf S,\mathbf A,U,P,c)$ be a controlled Markov process with Borel state and action spaces and a cost $c\ge0$ that is bounded on $\mathbf K$. Let $\pi^*\in\Pi_{SD}$ and $\rho,h\in\mathcal M_b(\mathbf S)$ satisfy (6.6) and (6.7) with $\pi^*(x)$ attaining both infima (as in the previous item). Let $N\in\mathbb N_0$ and suppose that $J_N(y,\pi^*,h)=h(y)+N\rho(y)$ for all $y\in\mathbf S$. Then for every $x\in\mathbf S$,
--   $$J_{N+1}(x,\pi^*,h)=h(x)+(N+1)\rho(x)\qquad\text{and}\qquad J^*_{N+1}(x,h)\le h(x)+(N+1)\rho(x).$$
--
--   This is the second display of the sufficiency part of the proof of Theorem 6.2 (the induction step for the upper bound), with the step from $N-1$ to $N$ written as the step from $N$ to $N+1$. Together with the lower bound it gives $J_N(x,\pi^*,h)=J^*_N(x,h)=h(x)+N\rho(x)$ for all $N$, i.e. that $(\rho,h,\pi^*)$ is canonical.
--
--   **Formalization Note.** The paper prints the integrand of the second line as $J^*_{N-1}(y,\pi^*,h)$; the quantity meant (and used in the next line) is $J_{N-1}(y,\pi^*,h)$, the cost of $\pi^*$, which this item uses. The induction hypothesis is stated for $J_N(\cdot,\pi^*,h)$ only, which is all the step needs. (6.6), (6.7) are in attained form.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 317, proof of Theorem 6.2, Sufficiency, display after "On the other hand"

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP

open MeasureTheory ProbabilityTheory

namespace ArapostathisAC.CanonicalTriplet

theorem sufficiency_upper {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (πstar : StationaryPolicy M)
    (ρ h : S → ℝ) (hρ : IsBoundedMeas ρ) (hh : IsBoundedMeas h)
    (h66 : Eq66 M ρ πstar) (h67 : Eq67 M ρ h πstar) (N : ℕ)
    (hN : ∀ y, JN M πstar.toPolicy N h y = h y + N * ρ y) :
    ∀ x, JN M πstar.toPolicy (N + 1) h x = h x + ((N : ℝ) + 1) * ρ x ∧
      JNopt M (N + 1) h x ≤ h x + ((N : ℝ) + 1) * ρ x := by sorry

end ArapostathisAC.CanonicalTriplet
