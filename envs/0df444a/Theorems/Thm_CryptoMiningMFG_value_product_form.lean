-- Prove2me | Theorems.Thm_CryptoMiningMFG_value_product_form
-- name    : CryptoMiningMFG.value_product_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:53.58595+00:00
-- url     : https://prove2.me/theorems/5e4c3e22-bece-4a23-bd06-8749ed6c815c
-- title:
--   Proof of Prop. 3.1: the CARA value function is $U(x)h(t)$ and $\Delta v/\partial_x v=w(r;\gamma)$
-- statement:
--   Assume exponential utility $U(x)=-\frac1\gamma e^{-\gamma x}$. Let $\bar\alpha$ be **any** admissible mean hash rate (measurable, positive on $[t_0,T]$) and $t\in[t_0,T]$. Then:
--
--   1. there is a number $h>0$ such that, for every wealth $x\in\mathbb R$,
--   $$
--   v(t,x;\bar\alpha)=U(x)\,h;
--   $$
--   2. for every $x$, the function $v(t,\cdot;\bar\alpha)$ is differentiable at $x$, $\partial_x v(t,x;\bar\alpha)>0$, $\Delta v(t,x;\bar\alpha)=v(t,x+r;\bar\alpha)-v(t,x;\bar\alpha)>0$, and
--   $$
--   \frac{\Delta v(t,x;\bar\alpha)}{\partial_x v(t,x;\bar\alpha)}=w(r;\gamma)=\frac{1-e^{-\gamma r}}{\gamma}.
--   $$
--
--   Here $v$ is the value function (2.4), the supremum of expected utility over all controls. The paper guesses this product form for the equilibrium value function and validates it through the HJB equation; the statement here is about the value function itself, for every mean hash rate. It is what makes the feedback (2.6) independent of wealth.
--
--   Differences from the source:
--   - generalization: the ansatz v(t, x) = U(x)h(t) for the equilibrium value function, validated through the HJB equation (2.7) under the assumption that v is a classical solution → v(t, x; ᾱ) = U(x)·h with h > 0, differentiability in x, ∂ₓv > 0, Δv > 0 and Δv/∂ₓv = w(r;γ), for the value function (2.4) itself and for every admissible ᾱ; reason: the equilibrium ᾱ* is one admissible ᾱ, and the page's conclusion (Δv/∂ₓv = w does not depend on x) is the instance; the ODE for h is not stated
--   - reading: r is "the value of the mining reward" (p.9), sign not stated → 0 < r (field r_pos of Model); reason: a reward has positive value; with r ≤ 0 one has w ≤ 0 and no positive mean hash rate exists
--   - generalization: M + 1 is the total number of miners, M a positive integer "assumed large" (p.9) → M any positive real number; reason: nothing in §3.1 uses integrality; every integer M ≥ 1 is an instance
--   - generalization: the supremum in (2.4) is over Markovian controls α_t = α(t, X_t) (p.10) → the supremum is over all non-anticipating controls: measurable, locally integrable hash-rate rules φ_j(s; τ₁,…,τ_j) ≥ 0 of time and of the miner's own reward history; reason: this class contains every Markov control whose closed loop is well defined, and the optimum (the constant rate a*) is Markov, so at the equilibrium the two value functions coincide; for every admissible ᾱ both value functions have the product form U(x)h(t) (translation invariance), so Δv/∂ₓv = w(r;γ) and (2.6) is the same in either class, and so are the equilibria
--   - encoding: E[U(X_T)] with U(x) = −(1/γ)e^{−γx} → −(1/γ) times the lower Lebesgue integral of e^{−γX_T} in [0, ∞], with the integrand set to 0 on the null event of infinitely many rewards by T; the reward process is built from i.i.d. Exp(1) clocks; reason: Lean convention; the event of infinitely many rewards has probability 0 because the intensity is at most 𝒦, so no instance changes
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, proof of Proposition 3.1, p.15 ("We guess the form v(t, x) = U(x)h(t) … this ansatz implies that Δv/∂ₓv does not depend on x")

import Mathlib
import Definitions.Def_CryptoMiningMFG_Admissible
import Definitions.Def_CryptoMiningMFG_Value

namespace CryptoMiningMFG

/-- **Product form of the CARA value function.** Li, Reppen, Sircar, *A Mean Field Games Model for
Cryptocurrency Mining*, arXiv:1912.01952v2, proof of Proposition 3.1, p.15: "We guess the form
v(t, x) = U(x)h(t) … Moreover, this ansatz implies that Δv/∂ₓv does not depend on x."

For exponential utility and **every** admissible mean hash rate `ᾱ` (measurable, positive on
`[t0, T]`) and every `t ∈ [t0, T]`:
1. there is `h > 0` with `v(t, x; ᾱ) = U(x) h` for all `x ∈ ℝ`;
2. for every `x`, `v(t, ·; ᾱ)` is differentiable at `x`, `∂ₓv(t, x; ᾱ) > 0`,
   `Δv(t, x; ᾱ) = v(t, x + r; ᾱ) − v(t, x; ᾱ) > 0`, and `Δv / ∂ₓv = w(r; γ)`.

Here `v` is the value function (2.4): the supremum of expected utility over all controls of the
reward process, not a solution of the HJB equation. -/
theorem value_product_form (P : Model) (abar : ℝ → ℝ) (habar : Admissible P abar)
    (t : ℝ) (ht : t ∈ Set.Icc P.t0 P.T) :
    (∃ h : ℝ, 0 < h ∧ ∀ x : ℝ, value P t x abar = P.U x * h) ∧
    ∀ x : ℝ, DifferentiableAt ℝ (fun y => value P t y abar) x ∧
      0 < deriv (fun y => value P t y abar) x ∧
      0 < value P t (x + P.r) abar - value P t x abar ∧
      (value P t (x + P.r) abar - value P t x abar) / deriv (fun y => value P t y abar) x
        = P.w := by sorry

end CryptoMiningMFG
