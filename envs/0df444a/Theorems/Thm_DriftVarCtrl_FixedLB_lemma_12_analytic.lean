-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_12_analytic
-- name    : DriftVarCtrl.FixedLB.lemma_12_analytic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:41.487588+00:00
-- url     : https://prove2.me/theorems/b401ccb0-389b-460f-82a4-ae606107d3ea
-- title:
--   Lemma 12 (analytic form), pp. EC-14–EC-15 — a C¹, piecewise C² supersolution of the HJB with V(0) = 0, V(U) = M lies below every policy value
-- statement:
--   Let $V : \mathbb R \to \mathbb R$ be continuously differentiable on $[0,U]$ and twice continuously differentiable at every point of $(0,U)$ outside a finite set $E$, with
--   $$V(0) = 0,\qquad V(U) = M,$$
--   and suppose that for every $x \in (0,U)\setminus E$
--   $$\min\Big\{h_1 + \mu_1V'(x) + \frac{\sigma_1^2}{2}V''(x),\ h_2 + \mu_2V'(x) + \frac{\sigma_2^2}{2}V''(x)\Big\} \ge 0 .$$
--   Then for every interval policy $\pi$ and every value $W$ of $\pi$,
--   $$V(x) \le W(x)\qquad\text{for all } x \in [0,U].$$
--
--   This is the verification step of the paper: a function satisfying the HJB inequality (94) and the boundary conditions (93) is a lower bound for the cost of every policy. Combined with a policy whose value satisfies the HJB inequality, it proves that policy optimal.
--
--   **Formalization Note.** In the paper the right-hand side of (95) is the expected cost $E_x[\int_0^T h(A(t))\,dt + M\mathbf 1_{\{X(T)=U\}}]$ of an arbitrary admissible control; here it is the analytic value $W$ of an interval policy (the mission's encoding of the value), because Itô's formula is not available in Mathlib. The page's hypotheses "$V, V', V''$ bounded" are replaced by $C^1$ on the closed interval (which bounds $V, V'$) and $C^2$ off a finite set; "piecewise $C^2$" is read as $C^2$ off finitely many points.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-14–EC-15, Lemma 12 (verification lemma), (93)–(95), in analytic form

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model

namespace DriftVarCtrl.FixedLB

/-- Lemma 12, analytic form (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-14–EC-15, (93)–(95)). Let `V` be `C¹` on `[0, U]` and `C²`
off a finite set `E`, with `V(0) = 0`, `V(U) = M` (93) and
`min{h₁ + μ₁V′ + σ₁²/2·V″, h₂ + μ₂V′ + σ₂²/2·V″} ≥ 0` on `(0, U) \ E` (94). Then `V ≤ W` on `[0, U]` for
the value `W` of every interval policy.

Formalization Note: the right-hand side of (95), the expected cost of an admissible control, is
replaced by the analytic value `W` of an interval policy (`IsValue`); the stochastic statement
needs Itô's formula, which Mathlib lacks. The boundedness of `V, V′, V″` on the page is implied
by `C¹` on the compact interval for `V, V′` and is dropped for `V″`. -/
theorem lemma_12_analytic (p : Params) (V : ℝ → ℝ) (E : Finset ℝ)
    (hV1 : ContDiffOn ℝ 1 V (Set.Icc 0 p.U))
    (hV2 : ∀ x ∈ Set.Ioo 0 p.U, x ∉ E → ContDiffAt ℝ 2 V x)
    (h0 : V 0 = 0) (hUM : V p.U = p.M)
    (hHJB : ∀ x ∈ Set.Ioo 0 p.U, x ∉ E → ∀ c : Ctrl,
      0 ≤ p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x)
    (π : IntervalPolicy p) (W : ℝ → ℝ) (hW : IsValue p π W) :
    ∀ x ∈ Set.Icc 0 p.U, V x ≤ W x := by sorry

end DriftVarCtrl.FixedLB
