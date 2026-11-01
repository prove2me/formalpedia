-- Prove2me | Theorems.Thm_DelayedGLCB_eq_40
-- name    : DelayedGLCB.eq_40
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:54.377883+00:00
-- url     : https://prove2.me/theorems/230cbe09-d7f6-47a2-a7c3-8f699775c889
-- title:
--   (40) — one-step regret on the confidence event
-- statement:
--   Run DUCB-GLCB with an arg max tie-break. Fix an outcome $\omega$, a parameter $\theta^*$, a round $t>\tau$ at which $V_t$ is positive definite and $\|\hat\theta_t-\theta^*\|_{V_t}\le\beta_t$, and an arm $b$ with $X^*_t=x_{t,b}$. Then
--   $$
--   \langle X^*_t,\theta^*\rangle-\langle X_t,\theta^*\rangle\le\beta_t\big(\|X_t\|_{V_t^{-1}}-\|X^*_t\|_{V_t^{-1}}+\|X^*_t-X_t\|_{V_t^{-1}}\big).
--   $$
--
--   On the confidence event, the one-step regret is controlled by $\beta_t$ times the widths of the played and comparator features.
--
--   Differences from the source:
--   - generalization: the optimal arm a*_t, X*_t = x_{t,a*_t} → any comparator arm b, X*_t = x_{t,b}; reason: the step never uses optimality of a*_t; a*_t is an instance
--   - encoding: ‖·‖_{V_t^{-1}} at a round t > τ → hypothesis that V_t is positive definite; V_t^{-1} is Matrix.inv; reason: the weighted norm needs V_t invertible; the condition only excludes the undefined case
--   - encoding: a_t = arg max_a (x'_{t,a}θ̂_t + β_t‖x_{t,a}‖_{V_t^{-1}}) → a deterministic tie-break tie with v b ≤ v (tie v) for all b; reason: any arg max rule is such a tie-break
--   - reading: the event E_t (not defined on the page) → ‖θ̂_t − θ*‖_{V_t} ≤ β_t; reason: E_t is the confidence event that (37) establishes, the hypothesis used to pass from (36) to (40)
--   - generalization: θ* the true parameter → any θ* ∈ ℝ^d; reason: the step is deterministic
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, proof of Theorem 1, (40), p.26

import Mathlib
import Definitions.Def_DelayedGLCB_DUCB

namespace DelayedGLCB

open Matrix

/-- **One-step regret on the confidence event (40).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, proof of Theorem 1, (40), p.26: "If `E_t` holds for all
`t ≥ τ`, then, `⟨X*_t, θ*⟩ − ⟨X_t, θ*⟩ ≤ β_t (‖X_t‖_{V_t^{-1}} − ‖X*_t‖_{V_t^{-1}} + ‖X*_t − X_t‖_{V_t^{-1}})`."

For every outcome `ω`, every round `t > τ` at which `V_t` is positive definite and
`‖θ̂_t − θ*‖_{V_t} ≤ β_t` (the confidence event `E_t`), and every comparator arm `b`, the run of
DUCB-GLCB (argmax tie-break) satisfies (40) with `X*_t = x_{t,b}`.

**Formalization Note.** The event `E_t` is `‖θ̂_t − θ*‖_{V_t} ≤ β_t`, the conclusion of (37). Any
comparator arm is allowed in place of `a*_t`. Deterministic. -/
theorem eq_40 {Ω : Type*} {d K : ℕ} (A : DUCB d K) (E : Env Ω d K) (ω : Ω)
    (θstar : Fin d → ℝ) (hA : IsArgmaxSelector A.tie) (t : ℕ) (ht : A.τ < t)
    (hV : (V A E ω t).PosDef)
    (hconf : wnorm (V A E ω t) (thetaHat A E ω t - θstar) ≤ betaAt A E ω t) (b : Fin K) :
    E.x t ω b ⬝ᵥ θstar - X A E ω t ⬝ᵥ θstar
      ≤ betaAt A E ω t * (wnorm (V A E ω t)⁻¹ (X A E ω t) - wnorm (V A E ω t)⁻¹ (E.x t ω b)
          + wnorm (V A E ω t)⁻¹ (E.x t ω b - X A E ω t)) := by sorry

end DelayedGLCB
