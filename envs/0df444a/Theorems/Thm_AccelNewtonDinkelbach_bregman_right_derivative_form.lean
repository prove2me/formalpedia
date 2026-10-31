-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_bregman_right_derivative_form
-- name    : AccelNewtonDinkelbach.bregman_right_derivative_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:09.376002+00:00
-- url     : https://prove2.me/theorems/da7ad1da-ce98-466d-9afb-31783cd56a63
-- title:
--   Right derivative $g_+^{(i)}=\min\partial f(\delta^{(i)})$ and $D_f(\delta^*,\delta^{(i)})=f(\delta^{(i)})+g_+^{(i)}(\delta^*-\delta^{(i)})-f(\delta^*)$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function, let $\delta^*=\max(\{\delta:f(\delta)=0\}\cup\arg\max f)$ (assumed to exist), and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of a run of the Newton–Dinkelbach method in which each iteration is a standard update or a successful look-ahead (this covers Algorithm 1). Then for every $2\le i\le N$ the set $\partial f(\delta^{(i)})$ has a least element $g_+^{(i)}=\min_{g\in\partial f(\delta^{(i)})}g$ (the right derivative of $f$ at $\delta^{(i)}$), and
--
--   $$D_f(\delta^*,\delta^{(i)})=f(\delta^{(i)})+g_+^{(i)}\,(\delta^*-\delta^{(i)})-f(\delta^*),$$
--
--   a finite real number.
--
--   Since $\delta^*\le\delta^{(i)}$, the supremum in the Bregman divergence is attained at the smallest supergradient. This identity is the first step of the proof of Lemma 3.4 and turns the divergence at $\delta^{(i)}$ into an explicit expression.
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: D_f(δ′, δ) defined for δ, δ′ ∈ dom(f) with ∂f(δ) ≠ ∅, values in R̄ → total EReal-valued bregman dom f δ′ δ; reason: it is evaluated only at δ* and at iterates, which lie in dom and carry a supergradient; +∞ is the page's value of the supremum
--   - encoding: δ* := max({δ : f(δ) = 0} ∪ arg max f(δ)), assumed well defined → hypothesis IsDeltaStar dom f δstar (δstar is the greatest element of the roots and maximizers of f in dom); reason: the page's max is a greatest element; the hypothesis is exactly that it exists
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - generalization: Algorithm 1 (proof of Lemma 3.4) → every run of RelaxedStep: at each iteration either the standard update or a successful look-ahead, chosen freely; reason: runs of the standard method and of Algorithm 1 are relaxed runs (LookAheadStep implies RelaxedStep), so the statement specializes to both
--   - generalization: i > 2 → 2 ≤ i ≤ N; reason: the claim holds already at i = 2; it specializes to every i > 2
--   - encoding: g(i)+ = min_{g∈∂f(δ(i))} g → ∃ gp, IsLeast (superdiff dom f (δ i)) gp ∧ …; reason: the page presupposes that the minimum exists; the Lean statement asserts it
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, proof of Lemma 3.4, p.8 ("Let g(i)+ = min_{g∈∂f(δ(i))} g denote the right derivative of f at δ(i)"; "Since δ∗ ≤ δ(i), we see that Df(δ∗, δ(i)) = f(δ(i)) + g(i)+ (δ∗ − δ(i)) − f(δ∗)")

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_bregman
import Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
import Definitions.Def_AccelNewtonDinkelbach_RelaxedStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **The right derivative `g₊(i) = min ∂f(δ(i))` exists and `D_f(δ*, δ(i)) = f(δ(i)) + g₊(i)(δ* − δ(i)) − f(δ*)`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, proof of Lemma 3.4, p.8: "Let g(i)+ =
min_{g∈∂f(δ(i))} g denote the right derivative of f at δ(i)." and "Since δ∗ ≤ δ(i), we see that
Df(δ∗, δ(i)) = f(δ(i)) + g(i)+ (δ∗ − δ(i)) − f(δ∗)."

For every proper concave `f` (encoded as `(dom, f)`), every `δ*` as in `IsDeltaStar`, every run of
relaxed steps and every `2 ≤ i ≤ N`, the set `∂f(δ(i))` has a least element `g₊`, and
`D_f(δ*, δ(i))` is the real number `f(δ(i)) + g₊ (δ* − δ(i)) − f(δ*)`.

**Formalization Note** `i ≥ 2` as in the proof of Lemma 3.4 (which takes `i > 2`): at `i = 1` the
minimum need not exist. "`min`" is `IsLeast`. The identity is an equality in `EReal`; when
`δ(i) = δ*` both sides are `0`. Relaxed runs include Algorithm 1. -/
theorem bregman_right_derivative_form (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δstar : ℝ) (hstar : IsDeltaStar dom f δstar)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (RelaxedStep dom f) dom f δ g N)
    (i : ℕ) (hi : 2 ≤ i) (hiN : i ≤ N) :
    ∃ gp : ℝ, IsLeast (superdiff dom f (δ i)) gp ∧
      bregman dom f δstar (δ i) = ((f (δ i) + gp * (δstar - δ i) - f δstar : ℝ) : EReal) := by sorry

end AccelNewtonDinkelbach
