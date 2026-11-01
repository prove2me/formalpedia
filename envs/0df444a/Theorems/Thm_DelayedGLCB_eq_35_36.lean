-- Prove2me | Theorems.Thm_DelayedGLCB_eq_35_36
-- name    : DelayedGLCB.eq_35_36
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:52.483795+00:00
-- url     : https://prove2.me/theorems/6067b337-a1f3-42ff-b3f4-eb075e5e10da
-- title:
--   (35)–(36) — one-step decomposition from the UCB choice
-- statement:
--   Run DUCB-GLCB with an arg max tie-break. Fix an outcome $\omega$, a parameter $\theta^*$, a round $t>\tau$ at which $V_t$ is positive definite, and an arm $b$ with feature $X^*_t=x_{t,b}$. Write $X_t$ for the played feature, $\hat\theta_t$ for the estimate and $\Delta=\hat\theta_t-\theta^*$. Then
--   $$
--   \langle X^*_t,\theta^*\rangle-\langle X_t,\theta^*\rangle=\langle X^*_t-X_t,\hat\theta_t\rangle-\langle X^*_t-X_t,\hat\theta_t-\theta^*\rangle
--   $$
--   and
--   $$
--   \langle X^*_t,\theta^*\rangle-\langle X_t,\theta^*\rangle\le\beta_t\big(\|X_t\|_{V_t^{-1}}-\|X^*_t\|_{V_t^{-1}}\big)+\|X^*_t-X_t\|_{V_t^{-1}}\|\Delta\|_{V_t}.
--   $$
--
--   This reduces the one-step regret to the confidence radius $\|\Delta\|_{V_t}$ and the widths $\|X\|_{V_t^{-1}}$.
--
--   Differences from the source:
--   - generalization: the optimal arm a*_t, X*_t = x_{t,a*_t} → any comparator arm b, X*_t = x_{t,b}; reason: the step never uses optimality of a*_t; a*_t is an instance
--   - encoding: ‖·‖_{V_t^{-1}} at a round t > τ → hypothesis that V_t is positive definite; V_t^{-1} is Matrix.inv; reason: the weighted norm needs V_t invertible; the condition only excludes the undefined case
--   - encoding: a_t = arg max_a (x'_{t,a}θ̂_t + β_t‖x_{t,a}‖_{V_t^{-1}}) → a deterministic tie-break tie with v b ≤ v (tie v) for all b; reason: any arg max rule is such a tie-break
--   - generalization: θ* the true parameter → any θ* ∈ ℝ^d; reason: the step is deterministic and uses no property of θ*
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, proof of Theorem 1, (35)–(36), p.25

import Mathlib
import Definitions.Def_DelayedGLCB_DUCB

namespace DelayedGLCB

open Matrix

/-- **One-step decomposition (35)–(36).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, proof of Theorem 1, (35)–(36), p.25: "The selection of `a_t` in
DUCB-GLCB implies `⟨X*_t, θ̂_t⟩ + β_t ‖X*_t‖_{V_t^{-1}} ≤ ⟨X_t, θ̂_t⟩ + β_t ‖X_t‖_{V_t^{-1}}`. Then we have
`⟨X*_t, θ*⟩ − ⟨X_t, θ*⟩ = ⟨X*_t − X_t, θ̂_t⟩ − ⟨X*_t − X_t, θ̂_t − θ*⟩` (35)
`≤ β_t(‖X_t‖_{V_t^{-1}} − ‖X*_t‖_{V_t^{-1}}) + ‖X*_t − X_t‖_{V_t^{-1}} ‖∆‖_{V_t}`. (36)"

For every outcome `ω`, every round `t > τ` at which `V_t` is positive definite, and every comparator
arm `b` with `X*_t = x_{t,b}`, both the identity (35) and the inequality (36) hold for the run of
DUCB-GLCB (with an argmax tie-break), where `∆ = θ̂_t − θ*`.

**Formalization Note.** The paper's comparator is the optimal arm `a*_t`; any arm `b` is allowed
here. `V_t^{-1}` is `Matrix.inv`; `‖v‖_A = wnorm A v`. The statement is deterministic. -/
theorem eq_35_36 {Ω : Type*} {d K : ℕ} (A : DUCB d K) (E : Env Ω d K) (ω : Ω)
    (θstar : Fin d → ℝ) (hA : IsArgmaxSelector A.tie) (t : ℕ) (ht : A.τ < t)
    (hV : (V A E ω t).PosDef) (b : Fin K) :
    (E.x t ω b ⬝ᵥ θstar - X A E ω t ⬝ᵥ θstar
        = (E.x t ω b - X A E ω t) ⬝ᵥ thetaHat A E ω t
          - (E.x t ω b - X A E ω t) ⬝ᵥ (thetaHat A E ω t - θstar)) ∧
    E.x t ω b ⬝ᵥ θstar - X A E ω t ⬝ᵥ θstar
      ≤ betaAt A E ω t * (wnorm (V A E ω t)⁻¹ (X A E ω t) - wnorm (V A E ω t)⁻¹ (E.x t ω b))
        + wnorm (V A E ω t)⁻¹ (E.x t ω b - X A E ω t)
          * wnorm (V A E ω t) (thetaHat A E ω t - θstar) := by sorry

end DelayedGLCB
