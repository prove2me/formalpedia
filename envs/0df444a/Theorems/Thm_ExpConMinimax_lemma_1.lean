-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_1
-- name    : ExpConMinimax.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:52:46.44635+00:00
-- url     : https://prove2.me/theorems/2162cf12-73ed-4369-a84a-d1d09026d08f
-- title:
--   Lemma 1 — $F(x,y^*)-F(x^*,y)\ge-\|\gamma^*\|\|H(x)_+\|-\|\lambda^*\|\|G(y)_+\|$
-- statement:
--   Let $(x^*,y^*,\gamma^*,\lambda^*)$ be a saddle point of (2.1) for the problem (1.2) under the standing assumptions. Then for every $x\in\mathcal X$ and $y\in\mathcal Y$,
--   $$F(x,y^*)-F(x^*,y)\ \ge\ -\|\gamma^*\|\,\|H(x)_+\|-\|\lambda^*\|\,\|G(y)_+\|\ \ge\ -\max\{\|\gamma^*\|,\|\lambda^*\|\}\,\big(\|H(x)_+\|+\|G(y)_+\|\big).$$
--
--   Since an approximate solution need not be feasible, the objective gap $F(\bar x,y^*)-F(x^*,\bar y)$ can be negative; this lemma bounds it from below by the feasibility residuals, which gives the lower half of the two-sided rate in Theorem 9.
--
--   Differences from the source:
--   - generalization: $F=\mathbb E_\omega f$, $H=\mathbb E_\xi h$, $G=\mathbb E_\zeta g$ → $F$, $H$, $G$ are given functions; $f,h,g$ enter only through the oracle maps, whose means are tied to $F,H,G$ by Assumptions 2.1–2.2; reason: every instance of the paper (with $F:=\mathbb E f$, etc.) is an instance of the Lean statement
--   - generalization: convexity of $F(\cdot,y)$, $-F(x,\cdot)$, $H_i$, $G_j$ → required only on $\mathcal X$, resp. $\mathcal Y$; reason: weaker hypothesis; global convexity implies it
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 1, p.8 (proof in App. A.1, p.26)

import Mathlib
import Definitions.Def_ExpConMinimax_IsSaddlePoint

namespace ExpConMinimax

/-- **Lemma 1** (lower bound on the objective gap by the feasibility residuals).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 1, p.8:

"For any `x ∈ X` and `y ∈ Y`, it holds that
`F(x,y*) − F(x*,y) ≥ −‖γ*‖‖H(x)₊‖ − ‖λ*‖‖G(y)₊‖ ≥ −max{‖γ*‖,‖λ*‖}{‖H(x)₊‖ + ‖G(y)₊‖}`."

Here `(x*,y*,γ*,λ*)` is a saddle point of (2.1) in the sense of (2.2) (p.26: "Recall that
`(x*,y*,γ*,λ*)` is a saddle point to problem (2.1)").

**Formalization Note.** Both inequalities of the chain are stated. `H(x)₊` is the
componentwise positive part `vecPosPart`. -/
theorem lemma_1 {dx dy m₁ m₂ : ℕ} (P : Problem dx dy m₁ m₂) (hP : P.Standing)
    (xs : Vec dx) (ys : Vec dy) (γs : Vec m₁) (lams : Vec m₂)
    (hsad : IsSaddlePoint P xs ys γs lams) :
    ∀ x ∈ P.X, ∀ y ∈ P.Y,
      -(‖γs‖ * ‖vecPosPart (P.H x)‖) - ‖lams‖ * ‖vecPosPart (P.G y)‖ ≤ P.F x ys - P.F xs y ∧
      -(max ‖γs‖ ‖lams‖ * (‖vecPosPart (P.H x)‖ + ‖vecPosPart (P.G y)‖)) ≤
        -(‖γs‖ * ‖vecPosPart (P.H x)‖) - ‖lams‖ * ‖vecPosPart (P.G y)‖ := by sorry

end ExpConMinimax
