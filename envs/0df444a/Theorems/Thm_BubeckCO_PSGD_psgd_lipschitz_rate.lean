-- Prove2me | Theorems.Thm_BubeckCO_PSGD_psgd_lipschitz_rate
-- name    : BubeckCO.PSGD.psgd_lipschitz_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:02.419527+00:00
-- url     : https://prove2.me/theorems/4c6afc30-8d60-4059-8088-04920c959671
-- title:
--   Theorem 3.2 — $RL/\sqrt{t}$ rate of projected subgradient descent for Lipschitz functions
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be compact and convex, and let $f : X \to \mathbb{R}$ have a non-empty subdifferential $\partial f(x)$ (Definition 1.2) at every $x \in X$. Let $R, L \in \mathbb{R}$ and $t \ge 1$, and let $x_1, x_2, \dots$, $g_1, g_2, \dots$ be a run of projected subgradient descent
--
--   $$
--   y_{s+1} = x_s - \eta g_s,\quad g_s \in \partial f(x_s), \qquad x_{s+1} = \Pi_X(y_{s+1}), \qquad s = 1, \dots, t,
--   $$
--
--   with the constant step size $\eta = R/(L\sqrt t)$, such that
--
--   1. $\|z - x_1\| \le R$ for every $z \in X$ ($X$ lies in the Euclidean ball of radius $R$ centred at $x_1$);
--   2. $\|g_s\| \le L$ for $s = 1, \dots, t$.
--
--   Then for every $x^* \in X$, in particular for a minimizer of $f$ on $X$,
--
--   $$
--   f\Big(\frac{1}{t}\sum_{s=1}^{t} x_s\Big) - f(x^*) \le \frac{RL}{\sqrt t} .
--   $$
--
--   This is the dimension-free $O(1/\sqrt t)$ rate of the projected subgradient method for Lipschitz convex functions over a bounded convex set; by Section 3.5 of the monograph it cannot be improved by any black-box first-order method.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, indices are 1-based, and the subgradients $g_s$ are an arbitrary sequence constrained only by the run and by the bound $\|g_s\| \le L$. The existence of subgradients on all of $X$ is the hypothesis that makes $f$ convex on $X$.
--
--   Differences from the source:
--   - encoding: f : X → ℝ → f : ℝⁿ → ℝ (values off X never read); reason: Lean functions are total; every hypothesis and the conclusion evaluate f only at points of X, so the instances are the same
--   - generalization: X is contained in a Euclidean ball centred at x_1 ∈ X of radius R → ‖z − x 1‖ ≤ R for every z ∈ X (closed ball); reason: containment in the open ball implies containment in the closed ball, so the book's hypothesis implies the Lean one
--   - generalization: for any x ∈ X and any g ∈ ∂f(x), ‖g‖ ≤ L → ‖g s‖ ≤ L for the subgradients g_1, …, g_t used by the run; reason: with Definition 1.2 (subgradients relative to X) the printed hypothesis has no instance for n ≥ 1: at a maximizer of a linear functional cᵀy over X, g + kc ∈ ∂f(x̄) for every k ≥ 0 (e.g. n = 1, X = [0,1], f ≡ 0, ∂f(1) = [0,∞)), so the printed theorem is vacuous; the Lean hypothesis is implied by the printed one and by the reading 'subgradients of f on ℝⁿ', so it specializes to the book under every reading
--   - generalization: η = R/(L√t), defined for L > 0 → no positivity hypothesis on L or R; Lean's R/(L·√t) = 0 at L = 0; reason: R ≥ 0 and L ≥ 0 already follow from the hypotheses (t ≥ 1); at L = 0 all g_s = 0, the run stays at x_1 and 0 ∈ ∂f(x_1), so the conclusion holds there; for L > 0 the statement is the book's
--   - encoding: the method iterates (3.2)–(3.3) for every t ≥ 1 (infinite run) → IsPSGDRun constrains steps 1, …, t only; reason: the statement involves only x_1, …, x_{t+1} and g_1, …, g_t, and every finite run extends to an infinite one
--   - encoding: horizon t in (1/t)∑_{s=1}^t and √t → hypothesis 1 ≤ t; reason: at t = 0 the average (1/t)∑ and the step size R/(L√t) are undefined; the condition only excludes this case
--   - generalization: x* a minimizer of f on X (Notation, p. 242) → any point xstar ∈ X; reason: minimality of x* is not used; taking xstar to be the minimizer recovers the book's statement
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, pp. 264–265 (PDF pp. 37–38), Theorem 3.2, with the standing assumptions of Chapter 3 (pp. 262–263: Euclidean norm, X compact and convex) and §3.1 (pp. 263–264: X in a ball of radius R centred at x_1 ∈ X, ∂f(x) ≠ ∅ and ‖g‖ ≤ L)

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_BubeckCO_PSGD_IsPSGDRun

namespace BubeckCO.PSGD

/-- **Theorem 3.2 (rate of projected subgradient descent for Lipschitz functions).**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
pp. 264–265 (PDF pp. 37–38), Theorem 3.2: "The projected subgradient descent method with
`η = R/(L√t)` satisfies `f((1/t) ∑_{s=1}^t x_s) − f(x*) ≤ RL/√t`."

Standing assumptions (Chapter 3, pp. 262–263; §3.1, pp. 263–264): `X ⊂ ℝⁿ` is compact and
convex, contained in the Euclidean ball of radius `R` centred at `x_1 ∈ X`, and `∂f(x) ≠ ∅` for
every `x ∈ X`. Run (3.2)–(3.3) for `t ≥ 1` steps with `η = R/(L√t)`, the subgradients used
satisfying `‖g_s‖ ≤ L`. Then for every `x* ∈ X`,
`f((1/t) ∑_{s=1}^t x_s) − f(x*) ≤ RL/√t`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; indices are 1-based. Subgradients are
relative to `X` (Definition 1.2). With that definition the printed hypothesis "`‖g‖ ≤ L` for all
`x ∈ X` and all `g ∈ ∂f(x)`" has no instance when `n ≥ 1` (normal-cone directions can be added to
any subgradient at a maximizer of a linear functional over `X`, e.g. `X = [0,1]`, `f ≡ 0`,
`∂f(1) = [0, ∞)`), so the bound is imposed only on the subgradients `g_1, …, g_t` the method uses;
this is implied by the printed hypothesis. `x*` may be any point of `X` (the bound specializes to
the minimizer). The ball is the closed ball. No positivity of `R` or `L` is assumed: `R ≥ 0`
and `L ≥ 0` follow from the hypotheses, and at `L = 0` Lean's `R / 0 = 0` gives `η = 0`, where
the statement still holds (all `g_s = 0`, the run stays at `x_1`, and `0 ∈ ∂f(x_1)`). -/
theorem psgd_lipschitz_rate {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcompact : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hsub : ∀ z ∈ X, ∃ gz, IsSubgradient X f z gz)
    (R L : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) (ht : 1 ≤ t)
    (hR : ∀ z ∈ X, ‖z - x 1‖ ≤ R)
    (hL : ∀ s ∈ Finset.Icc 1 t, ‖g s‖ ≤ L)
    (hrun : IsPSGDRun X f (R / (L * Real.sqrt t)) x g t)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤ R * L / Real.sqrt t := by sorry

end BubeckCO.PSGD
