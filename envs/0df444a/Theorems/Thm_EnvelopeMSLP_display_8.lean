-- Prove2me | Theorems.Thm_EnvelopeMSLP_display_8
-- name    : EnvelopeMSLP.display_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:59.313739+00:00
-- url     : https://prove2.me/theorems/40336b91-551e-4282-bb89-d8e494ea4578
-- title:
--   Display (8) — the dynamic programming formulation of (7)
-- statement:
--   The optimal value of (7) satisfies, in the extended reals,
--   $$V_0(\theta)=\mathbb E\big[V_1(x_0,\xi_1,\theta)\big],$$
--   where the $V_t$ are given by the backward recursion
--   $$V_t(x_{t-1},\xi_t,\theta)=\max_{x_t}\ \langle c_t(\theta),x_t\rangle+\mathbb E[V_{t+1}(x_t,\xi_{t+1},\theta)\mid\xi^t]\quad\text{s.t. }W_t(\theta)x_t+T_t(\theta)x_{t-1}\le h_t(\theta),$$
--   with terminal condition $V_{T+1}\equiv0$ and $x_0$ given.
--
--   **Formalization Note** The right-hand side is `P.postValue θ 0 P.x0 ω`, which does not depend on $\omega$. Infeasibility and unboundedness are tracked by $\pm\infty$; a child with value $-\infty$ absorbs any $+\infty$ of another child.
--
--   Differences from the source:
--   - reading: the problem can be rewritten in its dynamic programming formulation → the value of (7) equals the expectation of V₁ at x₀, in EReal; reason: this is the equality that the sentence asserts, including the infeasible and unbounded cases
--   - reading: V_t(x_{t−1}, ξ_t, θ) → a function of the history node; reason: (8) conditions on ξ^t, and no Markov assumption is made
--   - encoding: a discrete process ξ on a probability space (Ω, F, P) → a finite scenario type Ω with p(ω) > 0 summing to 1; reason: this is the support of the law of ξ (p.12: finitely many atoms); a general space pushes forward onto it and the statement sees only the law
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (8), p.12

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_value
import Definitions.Def_EnvelopeMSLP_MSLP_postValue

namespace EnvelopeMSLP

/-- **Display (8): the dynamic programming formulation of (7).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (8), p.12. The value of (7)
in `EReal` equals the expectation of the first-stage value at the given `x₀`, for the backward recursion (8)
with terminal condition `V_{T+1} ≡ 0`.

**Formalization Note.** `P.postValue θ 0 P.x0 ω` is that expectation, and does not depend on `ω`, since the
empty history puts all scenarios in one class. The recursion itself is the definition of `postValue`. -/
theorem display_8 {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (ω : Ω) :
    P.value θ = P.postValue θ 0 P.x0 ω := by sorry

end EnvelopeMSLP
