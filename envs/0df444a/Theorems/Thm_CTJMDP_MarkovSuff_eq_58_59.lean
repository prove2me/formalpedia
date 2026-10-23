-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_eq_58_59
-- name    : CTJMDP.MarkovSuff.eq_58_59
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:46.281597+00:00
-- url     : https://prove2.me/theorems/c9f92fc8-38b6-4893-929c-9082f79102e7
-- title:
--   (58)–(59), p. 16 — P^σ̃_{x′}(t+u,Z,B) = (1 − e^{−u}) P^σ_γ(t,Z,B) for the extended policy σ̃, and for the Markov policy ϕ̃
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be an initial distribution and $u>0$. In the extended CTJMDP (54) with the added state $x'$ (jumping into $X$ with intensity $\gamma$ under action $a'$) and the absorbing action $a''$:
--
--   1. for every policy $\sigma$ with law $\mathbb P^\sigma_\gamma$, the policy $\tilde\sigma$ of (55) satisfies, for $t>0$, $Z\in\mathfrak B(X)$, $B\in\mathfrak B(A)$,
--   $$P^{\tilde\sigma}_{x'}(t+u,Z,B)=(1-e^{-u})\,P^\sigma_\gamma(t,Z,B);\qquad(58)$$
--   2. the same identity holds for a Markov policy $\phi$ and the Markov policy $\tilde\phi$ of p. 16 in place of $\sigma$ and $\tilde\sigma$.
--
--   Equivalently (59), $P^\sigma_\gamma(t,Z,B)=(1-e^{-u})^{-1}P^{\tilde\sigma}_{x'}(t+u,Z,B)$. This transfers statements about the initial distribution $\gamma$ to statements about the single initial state $x'$ in the extended model.
--
--   **Formalization Note** The sets $Z\subseteq X$ and $B\subseteq A$ are embedded into $X'$ and $A'$ by `Sum.inl`; the constant $1-e^{-u}$ is `ENNReal.ofReal (1 - Real.exp (-u))`, positive since $u>0$. For the Markov case the paper applies (59) to $\sigma=\phi$, whose $\tilde\sigma$ is the Markov policy $\tilde\phi$ ("defined uniquely", p. 16); the second item states it for $\tilde\phi$ directly.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 16, (58)–(59); (54)–(55), p. 15

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting
import Definitions.Def_CTJMDP_MarkovSuff_Extension

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- (58)–(59) (p. 16): `P^{σ̃}_{x′}(t + u, Z, B) = (1 − e^{−u}) P^σ_γ(t, Z, B)`, for a policy `σ` and for a
Markov policy `ϕ` (whose `σ̃` is the Markov policy `ϕ̃`). -/
theorem eq_58_59 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21) [Nonempty X]
    (gam : Measure X) [IsProbabilityMeasure gam] (u : ℝ) (hu : 0 < u) :
    (∀ (σ : Policy X A), IsPolicy M σ →
      ∀ (Psig : Measure (Traj X)) (Ptil : Measure (Traj (X ⊕ Unit))),
        IsLaw M gam σ Psig → IsLaw (extModel M gam) (Measure.dirac xPrime) (extPol σ u) Ptil →
        ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
          saMarg Ptil (extPol σ u) (t + u) (Sum.inl '' Z) (Sum.inl '' B) =
            ENNReal.ofReal (1 - Real.exp (-u)) * saMarg Psig σ t Z B) ∧
    (∀ (phi : X → ℝ → Measure A), IsMarkovPolicy M phi →
      ∀ (Pphi : Measure (Traj X)) (Ptil : Measure (Traj (X ⊕ Unit))),
        IsLaw M gam (markovPol phi) Pphi →
        IsLaw (extModel M gam) (Measure.dirac xPrime) (markovPol (extMarkov phi u)) Ptil →
        ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
          saMarg Ptil (markovPol (extMarkov phi u)) (t + u) (Sum.inl '' Z) (Sum.inl '' B) =
            ENNReal.ofReal (1 - Real.exp (-u)) * saMarg Pphi (markovPol phi) t Z B) := by sorry

end CTJMDP.MarkovSuff
