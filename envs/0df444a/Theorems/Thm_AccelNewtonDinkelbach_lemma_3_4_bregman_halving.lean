-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_lemma_3_4_bregman_halving
-- name    : AccelNewtonDinkelbach.lemma_3_4_bregman_halving
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:04.625492+00:00
-- url     : https://prove2.me/theorems/34de5750-834b-4217-b588-db93464b4705
-- title:
--   Lemma 3.4: Algorithm 1 halves $D_f(\delta^*,\delta^{(i)})$ every two iterations
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function, let $\delta^*=\max(\{\delta:f(\delta)=0\}\cup\arg\max f)$ (assumed to exist), and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of Algorithm 1 (Look-aheadNewton), started from any $\delta^{(1)}\in\operatorname{dom}(f)$ and $g^{(1)}\in\partial f(\delta^{(1)})$ with $f(\delta^{(1)})\le0$ and $g^{(1)}<0$, with arbitrary answers of the supergradient oracle. Let $D_f$ be the Bregman divergence of Definition 3.2. Then for every iteration $i>2$ (every $3\le i\le N$, including the last iterate),
--
--   $$D_f(\delta^*,\delta^{(i)})<\tfrac12\,D_f(\delta^*,\delta^{(i-2)}) .$$
--
--   The values are in $\bar{\mathbb R}$; $D_f(\delta^*,\delta^{(1)})$ may be $+\infty$, and then the right-hand side is $+\infty$.
--
--   This is the paper's key lemma on the look-ahead Newton–Dinkelbach method: the Bregman divergence to $\delta^*$ halves every two iterations. Combined with bounds on the initial and final divergence, it yields the paper's iteration bounds for linear fractional combinatorial optimization (Theorem 3.6) and for two variables per inequality systems (Theorem 4.11).
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: D_f(δ′, δ) defined for δ, δ′ ∈ dom(f) with ∂f(δ) ≠ ∅, values in R̄ → total EReal-valued bregman dom f δ′ δ; reason: it is evaluated only at δ* and at iterates, which lie in dom and carry a supergradient; +∞ is the page's value of the supremum
--   - encoding: δ* := max({δ : f(δ) = 0} ∪ arg max f(δ)), assumed well defined → hypothesis IsDeltaStar dom f δstar (δstar is the greatest element of the roots and maximizers of f in dom); reason: the page's max is a greatest element; the hypothesis is exactly that it exists
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - encoding: 1/2 Df(δ∗, δ(i−2)) → ((1/2 : ℝ) : EReal) * bregman dom f δstar (δ (i - 2)); reason: product in EReal; ½ · (+∞) = +∞, as on the page
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.4, p.8

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_bregman
import Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
import Definitions.Def_AccelNewtonDinkelbach_LookAheadStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **Lemma 3.4: the look-ahead Newton–Dinkelbach method halves the Bregman divergence every two iterations.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.4, p.8: "For every iteration i > 2 in
Algorithm 1, we have Df(δ∗, δ(i)) < 1/2 Df(δ∗, δ(i−2))."

For every proper concave `f : ℝ → ℝ̄` (encoded as `(dom, f)` with `f` concave on `dom`), every `δ*`
that is the greatest element of the roots and maximizers of `f`, every run `δ(1..N)`, `g(1..N)` of
Algorithm 1 with arbitrary oracle answers, and every `3 ≤ i ≤ N`:
`D_f(δ*, δ(i)) < ½ · D_f(δ*, δ(i−2))` in the extended reals.

**Formalization Note** `(dom, f)` encodes the proper concave `f`: `x ∉ dom` means `f(x) = −∞`.
`D_f` is `bregman`, `EReal`-valued; `D_f(δ*, δ(1))` is `+∞` when `δ(1)` is the right endpoint of
`dom` (then `½ · ⊤ = ⊤`). `δ*` is given by `IsDeltaStar` (the paper's `max`). Runs are 1-indexed
prefixes of executions of Algorithm 1 (`IsRun` with `LookAheadStep`), the oracle answers are
arbitrary at every call, and `i` ranges up to and including the last iterate `δ(N)`, which may be
`δ*`. -/
theorem lemma_3_4_bregman_halving (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δstar : ℝ) (hstar : IsDeltaStar dom f δstar)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (LookAheadStep dom f) dom f δ g N)
    (i : ℕ) (hi : 3 ≤ i) (hiN : i ≤ N) :
    bregman dom f δstar (δ i) < ((1 / 2 : ℝ) : EReal) * bregman dom f δstar (δ (i - 2)) := by sorry

end AccelNewtonDinkelbach
