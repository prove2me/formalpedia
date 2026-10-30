-- Prove2me | Theorems.Thm_BubeckCO_PSGD_psgd_sum_bound
-- name    : BubeckCO.PSGD.psgd_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:27:25.892144+00:00
-- url     : https://prove2.me/theorems/7ea44f3e-ccf7-48ac-8073-eecc9fcf31ab
-- title:
--   Proof of Theorem 3.2, last display — summed bound $R^2/(2\eta) + \eta L^2 t/2$
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be compact and convex, $f : X \to \mathbb{R}$, $R, L \in \mathbb{R}$, a fixed step size $\eta > 0$ and a horizon $t \ge 1$. Let $x_1, x_2, \dots$ and $g_1, g_2, \dots$ be a run of projected subgradient descent (3.2)–(3.3) for $t$ steps such that
--
--   1. $\|z - x_1\| \le R$ for every $z \in X$ ($X$ lies in the Euclidean ball of radius $R$ centred at $x_1$);
--   2. $\|g_s\| \le L$ for $s = 1, \dots, t$.
--
--   Then for every $x^* \in X$,
--
--   $$
--   \sum_{s=1}^{t} \big(f(x_s) - f(x^*)\big) \le \frac{R^2}{2\eta} + \frac{\eta L^2 t}{2} .
--   $$
--
--   This is the bound obtained in the proof of Theorem 3.2 by summing the one-step chain, using Lemma 3.1 to replace $\|y_{s+1} - x^*\|$ by $\|x_{s+1} - x^*\|$ and telescoping; the theorem follows by choosing $\eta = R/(L\sqrt t)$ and applying convexity.
--
--   **Formalization Note** Indices are 1-based (sums over $s \in \{1, \dots, t\}$); $x_1 \in X$ follows from the run.
--
--   Differences from the source:
--   - encoding: f : X → ℝ → f : ℝⁿ → ℝ (values off X never read); reason: Lean functions are total; every hypothesis and the conclusion evaluate f only at points of X, so the instances are the same
--   - generalization: step size η = R/(L√t) of Theorem 3.2 → any fixed step size η > 0; reason: the display is derived before the value of η is plugged in ('Plugging in the value of η directly gives the statement'); η > 0 is the book's convention (p. 262), and η = R/(L√t) is a special case
--   - generalization: X is contained in a Euclidean ball centred at x_1 ∈ X of radius R → ‖z − x 1‖ ≤ R for every z ∈ X (closed ball); reason: containment in the open ball implies containment in the closed ball, so the book's hypothesis implies the Lean one
--   - generalization: for any x ∈ X and any g ∈ ∂f(x), ‖g‖ ≤ L → ‖g s‖ ≤ L for the subgradients g_1, …, g_t used by the run; reason: with Definition 1.2 (subgradients relative to X) the printed hypothesis has no instance for n ≥ 1: at a maximizer of a linear functional cᵀy over X, g + kc ∈ ∂f(x̄) for every k ≥ 0 (e.g. n = 1, X = [0,1], f ≡ 0, ∂f(1) = [0,∞)), so the printed theorem is vacuous; the Lean hypothesis is implied by the printed one and by the reading 'subgradients of f on ℝⁿ', so it specializes to the book under every reading
--   - generalization: standing assumption ∂f(x) ≠ ∅ for every x ∈ X → not assumed; reason: this bound uses only the subgradients g_s of the run; the assumption is needed only for the Jensen step of Theorem 3.2
--   - encoding: the method iterates (3.2)–(3.3) for every t ≥ 1 (infinite run) → IsPSGDRun constrains steps 1, …, t only; reason: the statement involves only x_1, …, x_{t+1} and g_1, …, g_t, and every finite run extends to an infinite one
--   - encoding: horizon t of Theorem 3.2, whose proof this display belongs to (the method runs for t ≥ 1) → hypothesis 1 ≤ t; reason: the source's t is a number of iterations with t ≥ 1; at t = 0 the sum is empty and the bound is trivial, so the condition removes only that degenerate case
--   - generalization: x* a minimizer of f on X (Notation, p. 242) → any point xstar ∈ X; reason: minimality of x* is not used; taking xstar to be the minimizer recovers the book's statement
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 265 (PDF p. 38), proof of Theorem 3.2, last display (unnumbered)

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsPSGDRun

namespace BubeckCO.PSGD

/-- **Summed bound of projected subgradient descent (proof of Theorem 3.2, last display).**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 265 (PDF p. 38), proof of Theorem 3.2: "Summing the resulting inequality over `s`, and using
that `‖x_1 − x*‖ ≤ R` yield `∑_{s=1}^t (f(x_s) − f(x*)) ≤ R²/(2η) + ηL²t/2`."

Let `X ⊂ ℝⁿ` be compact and convex (Chapter 3), contained in the Euclidean ball of radius `R`
centred at `x_1` (§3.1). Run projected subgradient descent (3.2)–(3.3) with a fixed step size
`η > 0` for `t ≥ 1` steps, with subgradients satisfying `‖g_s‖ ≤ L`. Then for every `x* ∈ X`,
`∑_{s=1}^t (f(x_s) − f(x*)) ≤ R²/(2η) + η L² t / 2`.

**Formalization Note.** Indices are 1-based (`Finset.Icc 1 t`). The ball containment is the
closed ball `‖z − x_1‖ ≤ R` for `z ∈ X`; `x_1 ∈ X` follows from the run. The Lipschitz-type
bound is imposed on the subgradients the method uses, `‖g_s‖ ≤ L` for `1 ≤ s ≤ t`. The step
size is arbitrary (`η > 0`), not yet the value `R/(L√t)` of Theorem 3.2, and the standing
assumption `∂f(x) ≠ ∅` on `X` is not needed for this bound. `x*` may be any point of `X`. -/
theorem psgd_sum_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcompact : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R L η : ℝ) (hη : 0 < η)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) (ht : 1 ≤ t)
    (hR : ∀ z ∈ X, ‖z - x 1‖ ≤ R)
    (hL : ∀ s ∈ Finset.Icc 1 t, ‖g s‖ ≤ L)
    (hrun : IsPSGDRun X f η x g t)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤ R ^ 2 / (2 * η) + η * L ^ 2 * t / 2 := by sorry

end BubeckCO.PSGD
