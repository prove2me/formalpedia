-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_ext_disintegrates
-- name    : CTJMDP.MarkovSuff.ext_disintegrates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:41.515208+00:00
-- url     : https://prove2.me/theorems/ec0e3dc2-22d7-4503-85df-c9b386818e71
-- title:
--   Proof of Theorem 1, p. 16 — (19), hence (16), holds for ϕ̃, π̃ and the initial state x′ in the extended model
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be an initial distribution, $\pi$ a policy with law $\mathbb P^\pi_\gamma$, $\phi$ a Markov policy satisfying (16) for $(\gamma,\pi)$, and $u>0$. In the extended CTJMDP (54), let $\tilde\pi$ be the policy (55) built from $\pi$, $\tilde\phi$ the Markov policy of p. 16 built from $\phi$, and $\mathbb P^{\tilde\pi}_{x'}$ the law of $\tilde\pi$ from the added state $x'$. Then $\tilde\phi$ satisfies (16) for the initial state $x'$ and the policy $\tilde\pi$:
--   $$P^{\tilde\pi}_{x'}(t,Z,B)=\int_Z\tilde\phi(B\mid z,t)\,P^{\tilde\pi}_{x'}(t,dz),\qquad t>0,\ Z\in\mathfrak B(X'),\ B\in\mathfrak B(A').$$
--
--   This is the claim that lets Lemma 5 be applied to $(\tilde\pi,\tilde\phi)$ in the extended model, which together with (59) yields Theorem 1 for a general $\gamma$.
--
--   **Formalization Note** The paper verifies (19) for $(\tilde\phi,\tilde\pi,x')$ and concludes (16) by Corollary 1; the Lean statement asserts (16) directly.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 16, proof of Theorem 1 (display defining ϕ̃ and the claim after it)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting
import Definitions.Def_CTJMDP_MarkovSuff_Extension

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- p. 16: (19), equivalently (16), holds for `ϕ̃`, `π̃` and the initial state `x′`. -/
theorem ext_disintegrates {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21) [Nonempty X]
    (gam : Measure X) [IsProbabilityMeasure gam] (u : ℝ) (hu : 0 < u)
    (π : Policy X A) (hπ : IsPolicy M π)
    (Ppi : Measure (Traj X)) (hPpi : IsLaw M gam π Ppi)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (h16 : Disintegrates Ppi π phi)
    (Ptil : Measure (Traj (X ⊕ Unit)))
    (hPtil : IsLaw (extModel M gam) (Measure.dirac xPrime) (extPol π u) Ptil) :
    Disintegrates Ptil (extPol π u) (extMarkov phi u) := by sorry

end CTJMDP.MarkovSuff
