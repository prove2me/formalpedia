-- Prove2me | Theorems.Thm_DelayedGLCB_eq_42_first
-- name    : DelayedGLCB.eq_42_first
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:54.96527+00:00
-- url     : https://prove2.me/theorems/bd99faa4-4bb7-448a-93bd-468b15211f76
-- title:
--   (42), first inequality — $R_T\le\tau+L_g\sum_{t>\tau}(\langle X^*_t,\theta^*\rangle-\langle X_t,\theta^*\rangle)$
-- statement:
--   Fix an outcome at which every feature vector lies in the unit ball, a differentiable $g$ with $\dot g\le L_g$, a constant $\kappa>0$ with $\dot g(x'\theta^*)\ge\kappa$ for $\|x\|\le1$, and suppose $g(x'\theta^*)\in[0,1]$ for $\|x\|\le1$. Let $b_t$ be optimal arms, $g(x_{t,a}'\theta^*)\le g(x_{t,b_t}'\theta^*)$ for all $a$, and $X^*_t=x_{t,b_t}$. For every action process, every $\tau$ and every $T$,
--   $$
--   R_T\le\tau+L_g\sum_{t=\tau+1}^{T}\big(\langle X^*_t,\theta^*\rangle-\langle X_t,\theta^*\rangle\big).
--   $$
--
--   The exploration rounds cost at most one each, and afterwards the regret is the linear regret scaled by the Lipschitz constant of the link.
--
--   Differences from the source:
--   - reading: g is an increasing function → κ ≤ ġ(x'θ*) for ‖x‖ ≤ 1, with κ > 0; reason: this is Assumption 1's bound at θ = θ*; it makes the optimal arm maximize ⟨x, θ*⟩ as well, which the step needs (a merely non-decreasing g would not suffice)
--   - generalization: g bounded between 0 and 1 → g(x'θ*) ∈ [0, 1] for ‖x‖ ≤ 1; reason: only these values enter the regret
--   - encoding: g Lipschitz with constant L_g → g differentiable with ġ ≤ L_g; reason: Assumption 1's form of the constant
--   - generalization: the actions of DUCB-GLCB → any action process; reason: the step uses no property of the algorithm
--   - generalization: a*_t = arg max_a g(x'_{t,a}θ*) → any arms b_t maximizing g(x'_{t,a}θ*); reason: every arg max choice is such a b_t
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, proof of Theorem 1, (42), first inequality, p.27

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_DUCB

namespace DelayedGLCB

open Matrix MostlyExplorationFree.GreedyBandit

/-- **Regret reduction, first inequality of (42).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, proof of Theorem 1, (42), p.27: "Note that `g` is an increasing
Lipschitz function with Lipschitz constant `L_g` and the `g` function is bounded between 0 and 1. The
regret of algorithm DUCB-GLCB can be upper bounded as
`R_T ≤ τ + L_g Σ_{t=τ+1}^T (⟨X*_t, θ*⟩ − ⟨X_t, θ*⟩)`."

Fix an outcome `ω` at which every feature vector lies in the unit ball, a differentiable `g` with
`ġ ≤ L_g`, `κ > 0` with `κ ≤ ġ(x'θ*)` for `‖x‖ ≤ 1`, and `g(x'θ*) ∈ [0,1]` for `‖x‖ ≤ 1`. Let `b_t` be
optimal arms (`g(x_{t,a}'θ*) ≤ g(x_{t,b_t}'θ*)` for all `a`) and `X*_t = x_{t,b_t}`. Then for any
action process, any `τ` and `T`, `R_T ≤ τ + L_g Σ_{t=τ+1}^T (⟨X*_t, θ*⟩ − ⟨X_t, θ*⟩)`.

**Formalization Note.** "Increasing" is realized by Assumption 1's bound `κ ≤ ġ` at `θ = θ*`, which is
what makes `⟨X*_t, θ*⟩ ≥ ⟨X_t, θ*⟩`; "bounded between 0 and 1" is required only at `x'θ*`, `‖x‖ ≤ 1`.
The statement holds for any action process, in particular DUCB-GLCB's. Deterministic. -/
theorem eq_42_first {Ω : Type*} {d K : ℕ} (E : Env Ω d K) (g : ℝ → ℝ) (θstar : Fin d → ℝ)
    (κ Lg : ℝ) (act : ℕ → Ω → Fin K) (τ T : ℕ) (ω : Ω)
    (hx : ∀ t a, l2norm (E.x t ω a) ≤ 1) (hg : Differentiable ℝ g) (hκ : 0 < κ)
    (hκle : ∀ x : Fin d → ℝ, l2norm x ≤ 1 → κ ≤ deriv g (x ⬝ᵥ θstar))
    (hLg : ∀ z, deriv g z ≤ Lg)
    (hg01 : ∀ x : Fin d → ℝ, l2norm x ≤ 1 → g (x ⬝ᵥ θstar) ∈ Set.Icc (0 : ℝ) 1)
    (bstar : ℕ → Fin K) (hb : ∀ t a, g (E.x t ω a ⬝ᵥ θstar) ≤ g (E.x t ω (bstar t) ⬝ᵥ θstar)) :
    regret E g θstar act T ω
      ≤ τ + Lg * ∑ t ∈ Finset.Ioc τ T,
          (E.x t ω (bstar t) ⬝ᵥ θstar - E.x t ω (act t ω) ⬝ᵥ θstar) := by sorry

end DelayedGLCB
