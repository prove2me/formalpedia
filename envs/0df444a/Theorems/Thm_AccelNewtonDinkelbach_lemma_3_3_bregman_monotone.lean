-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_lemma_3_3_bregman_monotone
-- name    : AccelNewtonDinkelbach.lemma_3_3_bregman_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:52.178514+00:00
-- url     : https://prove2.me/theorems/2cac0553-8cd5-4fff-b0d2-ba573df034a3
-- title:
--   Lemma 3.3: $D_f(\delta^*,\delta^{(i)})\le D_f(\delta^*,\delta^{(i-1)})$, with the equality case
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function, let $\delta^*=\max(\{\delta:f(\delta)=0\}\cup\arg\max f)$ (assumed to exist), and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of a run of the Newton–Dinkelbach method in which each iteration is a standard update or a successful look-ahead (this covers the classical method and Algorithm 1). Let $D_f$ be the Bregman divergence of Definition 3.2. Then for every $2\le i\le N$,
--
--   $$D_f(\delta^*,\delta^{(i)})\le D_f(\delta^*,\delta^{(i-1)}),$$
--
--   with equality if and only if $g^{(i-1)}=\inf_{g\in\partial f(\delta^{(i-1)})}g$ and $f(\delta^{(i)})=0$. Values are in $\bar{\mathbb R}$: at $i=2$ the right-hand side may be $+\infty$, and then the inequality is strict.
--
--   The Bregman divergence to $\delta^*$ is therefore a potential that never increases along the run and strictly decreases except in the final iteration.
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: D_f(δ′, δ) defined for δ, δ′ ∈ dom(f) with ∂f(δ) ≠ ∅, values in R̄ → total EReal-valued bregman dom f δ′ δ; reason: it is evaluated only at δ* and at iterates, which lie in dom and carry a supergradient; +∞ is the page's value of the supremum
--   - encoding: δ* := max({δ : f(δ) = 0} ∪ arg max f(δ)), assumed well defined → hypothesis IsDeltaStar dom f δstar (δstar is the greatest element of the roots and maximizers of f in dom); reason: the page's max is a greatest element; the hypothesis is exactly that it exists
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - generalization: the standard Newton–Dinkelbach method of p.6, and Algorithm 1 (p.7) → every run of RelaxedStep: at each iteration either the standard update or a successful look-ahead, chosen freely; reason: runs of the standard method and of Algorithm 1 are relaxed runs (LookAheadStep implies RelaxedStep), so the statement specializes to both
--   - encoding: g(i−1) = inf_{g∈∂f(δ(i−1))} g → IsLeast (superdiff dom f (δ (i-1))) (g (i-1)); reason: g(i−1) ∈ ∂f(δ(i−1)), so equality with the inf is being the least element
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.3, p.7 (proof in Appendix A, p.27); p.7: "Lemmas 3.1 and 3.3 also hold for Algorithm 1"

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_bregman
import Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
import Definitions.Def_AccelNewtonDinkelbach_RelaxedStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **Lemma 3.3: the Bregman divergence to `δ*` is non-increasing along the run.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.3, p.7 (proof p.27): "For every iteration
i ≥ 2, we have Df(δ∗, δ(i)) ≤ Df(δ∗, δ(i−1)) which holds at equality if and only if
g(i−1) = inf_{g∈∂f(δ(i−1))} g and f(δ(i)) = 0."

For every proper concave `f` (encoded as `(dom, f)`), every `δ*` as in `IsDeltaStar`, every run of
relaxed steps and every `2 ≤ i ≤ N`: `D_f(δ*, δ(i)) ≤ D_f(δ*, δ(i−1))` in the extended reals, with
equality iff `g(i−1)` is the least element of `∂f(δ(i−1))` and `f(δ(i)) = 0`.

**Formalization Note** `D_f` is `EReal`-valued; at `i = 2` the right-hand side may be `+∞` (start at
the right endpoint of `dom`), and then the inequality is strict and `IsLeast` fails, as on the page.
"`g(i−1) = inf`" is `IsLeast`, equivalent since `g(i−1) ∈ ∂f(δ(i−1))`. Relaxed runs include the
standard method and Algorithm 1. -/
theorem lemma_3_3_bregman_monotone (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δstar : ℝ) (hstar : IsDeltaStar dom f δstar)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (RelaxedStep dom f) dom f δ g N)
    (i : ℕ) (hi : 2 ≤ i) (hiN : i ≤ N) :
    bregman dom f δstar (δ i) ≤ bregman dom f δstar (δ (i - 1)) ∧
      (bregman dom f δstar (δ i) = bregman dom f δstar (δ (i - 1)) ↔
        IsLeast (superdiff dom f (δ (i - 1))) (g (i - 1)) ∧ f (δ i) = 0) := by sorry

end AccelNewtonDinkelbach
