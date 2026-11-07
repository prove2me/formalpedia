-- Prove2me | Theorems.Thm_EffHorizonProphet_lemma_12
-- name    : EffHorizonProphet.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:44.387352+00:00
-- url     : https://prove2.me/theorems/2948a04d-3f9e-4014-ba41-6a751f01f6ee
-- title:
--   Lemma 12 — monotonicity of $y(x)$
-- statement:
--   Fix $S\ge1$ and $\tilde\gamma\in[0,1]$. The function $y:(0,\infty)\to\mathbb R$ of (21) is non-decreasing: $y'(x)\ge0$ for all $x>0$.
--
--   By the derivative factorization (24), this makes $f_S(\cdot,y_{\tilde\gamma})$ increasing before $x_{\tilde\gamma}$ and decreasing after it, which identifies the global maximum.
--
--   Differences from the source:
--   - encoding: $y^\prime(x)\ge0$ → $y$ is differentiable at $x$ with nonnegative derivative, and it is monotone on $(0,\infty)$; reason: the page states "non-decreasing" and differentiates; a Lean derivative alone would be $0$ at a non-differentiable point
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemma 12, p.23

import Mathlib
import Definitions.Def_EffHorizonProphet_yFun

namespace EffHorizonProphet

/-- **Lemma 12** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.23): for `γ̃ ∈ [0, 1]` the function `y` of (21) is non-decreasing on
`(0, ∞)`: `y'(x) ≥ 0` for all `x > 0`.

**Formalization Note** A bare `0 ≤ deriv` would hold by the junk value at a non-differentiable point,
so differentiability and `MonotoneOn` are stated as well. -/
theorem lemma_12 (S : ℕ) (hS : 1 ≤ S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ x, 0 < x → DifferentiableAt ℝ (yFun S γ) x ∧ 0 ≤ deriv (yFun S γ) x) ∧
      MonotoneOn (yFun S γ) (Set.Ioi 0) := by sorry

end EffHorizonProphet
