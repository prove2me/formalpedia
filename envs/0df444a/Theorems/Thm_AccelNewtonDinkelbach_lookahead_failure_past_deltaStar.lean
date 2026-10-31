-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_lookahead_failure_past_deltaStar
-- name    : AccelNewtonDinkelbach.lookahead_failure_past_deltaStar
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:45.873526+00:00
-- url     : https://prove2.me/theorems/5fec8cb9-6a58-404a-8715-83e034c04bfd
-- title:
--   After a failed look-ahead in Algorithm 1: $2\delta^{(i)}-\delta^{(i-1)}\le\delta^*$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function, let $\delta^*=\max(\{\delta:f(\delta)=0\}\cup\arg\max f)$ (assumed to exist), and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of Algorithm 1 (Look-aheadNewton), with arbitrary answers of the supergradient oracle. Let $2\le i\le N$ and suppose the look-ahead in iteration $i-1$ was unsuccessful, so that $\delta^{(i)}=\delta^{(i-1)}-f(\delta^{(i-1)})/g^{(i-1)}$ is the plain Newton–Dinkelbach point. Then
--
--   $$2\delta^{(i)}-\delta^{(i-1)}\le\delta^*,\qquad\text{equivalently}\qquad 2(\delta^{(i)}-\delta^*)\le\delta^{(i-1)}-\delta^* .$$
--
--   The look-ahead guess of iteration $i-1$ went past or exactly to $\delta^*$, so the plain step already covered at least half of the remaining distance to $\delta^*$. In the proof of Lemma 3.4 this yields $D_f(\delta^*,\delta^{(i-2)})>2D_f(\delta^*,\delta^{(i)})$. The statement uses Algorithm 1's rule: if the standard update could be taken although the look-ahead would succeed, it would fail.
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: δ* := max({δ : f(δ) = 0} ∪ arg max f(δ)), assumed well defined → hypothesis IsDeltaStar dom f δstar (δstar is the greatest element of the roots and maximizers of f in dom); reason: the page's max is a greatest element; the hypothesis is exactly that it exists
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - generalization: i > 2 → 2 ≤ i ≤ N; reason: the claim holds already at i = 2; it specializes to every i > 2
--   - encoding: the look-ahead step at iteration i − 1 was unsuccessful → δ(i) = newtonPoint f (δ(i−1)) (g(i−1)); reason: within a run of Algorithm 1 the successful branch gives δ(i) = 2d − δ(i−1) ≠ d, so δ(i) = d holds exactly when the look-ahead failed
--   - encoding: 2δ(i) − δ(i−1) ≤ δ∗ ⇔ 2(δ(i) − δ∗) ≤ δ(i−1) − δ∗ → 2 * δ i - δ (i-1) ≤ δstar; reason: the two forms are the same inequality rearranged
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, proof of Lemma 3.4, p.8 ("Now assume that the look-ahead step at iteration i − 1 was unsuccessful. This implies that 2δ(i) − δ(i−1) ≤ δ∗ ⇔ 2(δ(i) − δ∗) ≤ δ(i−1) − δ∗")

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
import Definitions.Def_AccelNewtonDinkelbach_newtonPoint
import Definitions.Def_AccelNewtonDinkelbach_LookAheadStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **After a failed look-ahead in Algorithm 1: `2δ(i) − δ(i−1) ≤ δ*`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, proof of Lemma 3.4, p.8: "Now assume that the
look-ahead step at iteration i − 1 was unsuccessful. This implies that 2δ(i) − δ(i−1) ≤ δ∗ ⇔
2(δ(i) − δ∗) ≤ δ(i−1) − δ∗, i.e. that the look-ahead step “went past or exactly to” δ∗."

For every proper concave `f` (encoded as `(dom, f)`), every `δ*` as in `IsDeltaStar`, every run of
**Algorithm 1** with arbitrary oracle answers, and every `2 ≤ i ≤ N` such that `δ(i)` is the plain
Newton point `δ(i−1) − f(δ(i−1))/g(i−1)` of iteration `i − 1`: `2 δ(i) − δ(i−1) ≤ δ*`, i.e. the
look-ahead guess of iteration `i − 1` lies at or to the left of `δ*`.

**Formalization Note** "The look-ahead step at iteration `i − 1` was unsuccessful" is written
`δ(i) = d` with `d` the Newton point: within a run of Algorithm 1 the successful branch gives
`δ(i) = 2d − δ(i−1) ≠ d`. The page's equivalent form `2(δ(i) − δ*) ≤ δ(i−1) − δ*` is the same
inequality rearranged. The claim needs Algorithm 1's rule: with a relaxed step (standard update
taken although the look-ahead would succeed) it can fail. -/
theorem lookahead_failure_past_deltaStar (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δstar : ℝ) (hstar : IsDeltaStar dom f δstar)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (LookAheadStep dom f) dom f δ g N)
    (i : ℕ) (hi : 2 ≤ i) (hiN : i ≤ N)
    (hfail : δ i = newtonPoint f (δ (i - 1)) (g (i - 1))) :
    2 * δ i - δ (i - 1) ≤ δstar := by sorry

end AccelNewtonDinkelbach
