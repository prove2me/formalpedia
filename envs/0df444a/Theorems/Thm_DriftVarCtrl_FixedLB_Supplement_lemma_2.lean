-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_2
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:36:43.047866+00:00
-- url     : https://prove2.me/theorems/07271816-d0c2-4091-afc9-839c44cf425e
-- title:
--   Lemma 2, p. 18 — a single control's fixed-boundary value is ≤ 0 on (0, U] iff h ≤ h⁺
-- statement:
--   Consider the fixed-lower-boundary model of the base mission and one of its controls $c$, with drift $\mu$, volatility $\sigma$, cost $h$ and threshold $h^+$ of (17). Let $W$ be the value of the single control policy that always uses $c$: $W(0)=0$, $W(U)=M$ and $h+\mu W'+\frac{\sigma^2}{2}W''=0$ on $(0,U)$.
--
--   1. If $h\le h^+$, then $W(x)\le0$ for every $x\in(0,U]$.
--   2. If $h>h^+$, then $W$ is positive on some interval in $(0,U]$: there are $0\le a<b\le U$ with $W(x)>0$ for all $x\in(a,b)$.
--
--   So with a single control the cost threshold at which abandoning early pays is $h^+$; the proof of Theorem 3 applies this to each control.
--
--   **Formalization Note** The value is the base mission's analytic `IsValue` of the static policy. The standing assumption $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - encoding: the value function associated with the single control policy (expected cost (2)) → any W with IsValue p (static p c) W, the analytic value of the base mission; reason: Mathlib has no stochastic integral; the lemma's proof uses the closed form (54) of exactly this boundary-value problem
--   - reading: positive for some interval in (0, U] → there are 0 ≤ a < b ≤ U with W > 0 on (a, b); reason: an interval of positivity inside (0, U]; the proof finds one next to 0
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 18, Lemma 2 (proof p. EC-20, (118)–(121))

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 2 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 18; proof p. EC-20). Consider a control `c` with cost `h ≤ h⁺`. Then the
value function of the single control policy that always uses `c` (fixed lower boundary `0`) is
non-positive on `(0, U]`. If `h > h⁺`, it is positive on some interval in `(0, U]`.

Formalization Note: "the value function associated with the single control policy" is any
`W` with `IsValue p (static p c) W` (the analytic value of the base model: the ODE of `c` on
`(0, U)`, `W(0) = 0`, `W(U) = M`); the lemma's proof uses its closed form (54). The standing
`v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_2 (p : Params) (hv : v p .one < v p .two) (c : Ctrl) :
    (p.cost c ≤ hplus p c → ∀ W : ℝ → ℝ, IsValue p (static p c) W →
      ∀ x ∈ Set.Ioc 0 p.U, W x ≤ 0) ∧
    (hplus p c < p.cost c → ∀ W : ℝ → ℝ, IsValue p (static p c) W →
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ p.U ∧ ∀ x ∈ Set.Ioo a b, 0 < W x) := by sorry

end DriftVarCtrl.FixedLB.Supplement
