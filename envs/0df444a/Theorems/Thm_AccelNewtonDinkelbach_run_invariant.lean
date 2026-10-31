-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_run_invariant
-- name    : AccelNewtonDinkelbach.run_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:23.39351+00:00
-- url     : https://prove2.me/theorems/e65aaace-6116-4488-ad9e-60867ac4318d
-- title:
--   Invariant of the Newton–Dinkelbach method: $g^{(i)}<0$ unless $f(\delta^{(i)})=0$, and then $\delta^{(i)}=\delta^*$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function, let $\delta^*=\max(\{\delta:f(\delta)=0\}\cup\arg\max f)$ (assumed to exist), and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of a Newton–Dinkelbach-type run: the input satisfies $\delta^{(1)}\in\operatorname{dom}(f)$, $f(\delta^{(1)})\le0$, $g^{(1)}\in\partial f(\delta^{(1)})$, $g^{(1)}<0$, and each later pair arises from the previous one by a standard Newton–Dinkelbach update or by a successful look-ahead. Then for every $1\le i\le N$:
--
--   1. $\delta^{(i)}\in\operatorname{dom}(f)$, $g^{(i)}\in\partial f(\delta^{(i)})$ and $f(\delta^{(i)})\le 0$;
--   2. if $f(\delta^{(i)})<0$ then $g^{(i)}<0$;
--   3. if $f(\delta^{(i)})=0$ then $\delta^{(i)}=\delta^*$.
--
--   This is the invariant behind the correctness of the method: the supergradient stays negative except possibly in the final iteration, where the method stops at a root, and that root is the largest one. It also guarantees that the Newton step $\delta^{(i)}-f(\delta^{(i)})/g^{(i)}$ never divides by zero.
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: δ* := max({δ : f(δ) = 0} ∪ arg max f(δ)), assumed well defined → hypothesis IsDeltaStar dom f δstar (δstar is the greatest element of the roots and maximizers of f in dom); reason: the page's max is a greatest element; the hypothesis is exactly that it exists
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - generalization: the standard Newton–Dinkelbach method of p.6 → every run of RelaxedStep: at each iteration either the standard update or a successful look-ahead, chosen freely; reason: runs of the standard method and of Algorithm 1 are relaxed runs (LookAheadStep implies RelaxedStep), so the statement specializes to both
--   - encoding: g(i) < 0 except possibly in the final iteration when f(δ(i)) = 0 → f(δ(i)) < 0 → g(i) < 0 for every iterate; reason: the loop stops exactly at the first iterate with f(δ(i)) = 0, so "not the final iteration" is f(δ(i)) < 0
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6 ("it maintains a point δ(i) ∈ dom(f) and a supergradient g(i) ∈ ∂f(δ(i)) where f(δ(i)) ≤ 0"; "observe that g(i) < 0 except possibly in the final iteration when f(δ(i)) = 0 … Indeed, δ(i) = δ∗ if f(δ(i)) = 0")

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
import Definitions.Def_AccelNewtonDinkelbach_RelaxedStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **Invariant of the Newton–Dinkelbach method: `g(i) < 0` unless `f(δ(i)) = 0`, and then `δ(i) = δ*`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6: "At the start of every iteration i ≥ 1, it
maintains a point δ(i) ∈ dom(f) and a supergradient g(i) ∈ ∂f(δ(i)) where f(δ(i)) ≤ 0." and
"According to this update rule, observe that g(i) < 0 except possibly in the final iteration when
f(δ(i)) = 0. This proves the correctness of the algorithm. Indeed, δ(i) = δ∗ if f(δ(i)) = 0."

For every proper concave `f` (encoded as `(dom, f)` with `f` concave on `dom`), every `δ*` as in
`IsDeltaStar`, every run `δ(1..N)`, `g(1..N)` of relaxed steps (standard Newton–Dinkelbach or
look-ahead updates), and every `1 ≤ i ≤ N`: `δ(i) ∈ dom`, `g(i) ∈ ∂f(δ(i))`, `f(δ(i)) ≤ 0`;
if `f(δ(i)) < 0` then `g(i) < 0`; and if `f(δ(i)) = 0` then `δ(i) = δ*`.

**Formalization Note** Only `i = 1` is assumed (the input of the algorithm); the other iterates
come from the step relation, which contains no monotonicity or sign assumption on `g`. Relaxed
runs include the runs of Algorithm 1. -/
theorem run_invariant (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δstar : ℝ) (hstar : IsDeltaStar dom f δstar)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (RelaxedStep dom f) dom f δ g N)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    δ i ∈ dom ∧ g i ∈ superdiff dom f (δ i) ∧ f (δ i) ≤ 0 ∧
      (f (δ i) < 0 → g i < 0) ∧ (f (δ i) = 0 → δ i = δstar) := by sorry

end AccelNewtonDinkelbach
