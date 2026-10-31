-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_lemma_3_1_monotonicity
-- name    : AccelNewtonDinkelbach.lemma_3_1_monotonicity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:51.868659+00:00
-- url     : https://prove2.me/theorems/42030540-d339-4d93-9d63-ba91ab366aa9
-- title:
--   Lemma 3.1: monotonicity of $\delta^{(i)}$, $f(\delta^{(i)})$ and $g^{(i)}$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function, let $\delta^*=\max(\{\delta:f(\delta)=0\}\cup\arg\max f)$ (assumed to exist), and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of a run of the Newton–Dinkelbach method in which each iteration is a standard update or a successful look-ahead (this covers the classical method and Algorithm 1). Then for every $2\le i\le N$:
--
--   1. $\delta^*\le\delta^{(i)}<\delta^{(i-1)}$;
--   2. $f(\delta^*)\ge f(\delta^{(i)})>f(\delta^{(i-1)})$;
--   3. $g^{(i)}\ge g^{(i-1)}$, with equality if and only if $g^{(i)}=\inf_{g\in\partial f(\delta^{(i)})}g$, $g^{(i-1)}=\sup_{g\in\partial f(\delta^{(i-1)})}g$ and $f(\delta^{(i)})=0$;
--   4. moreover,
--   $$\frac{f(\delta^{(i)})}{f(\delta^{(i-1)})}+\frac{g^{(i)}}{g^{(i-1)}}\le 1 .$$
--
--   The iterates decrease towards $\delta^*$, the function values increase, and the supergradients increase strictly except in the final iteration. Item 4 shows that $|f(\delta^{(i)})|$ or $|g^{(i)}|$ shrinks geometrically, the classical ingredient of iteration bounds for the Newton–Dinkelbach method.
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: δ* := max({δ : f(δ) = 0} ∪ arg max f(δ)), assumed well defined → hypothesis IsDeltaStar dom f δstar (δstar is the greatest element of the roots and maximizers of f in dom); reason: the page's max is a greatest element; the hypothesis is exactly that it exists
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - generalization: the standard Newton–Dinkelbach method of p.6, and Algorithm 1 (p.7) → every run of RelaxedStep: at each iteration either the standard update or a successful look-ahead, chosen freely; reason: runs of the standard method and of Algorithm 1 are relaxed runs (LookAheadStep implies RelaxedStep), so the statement specializes to both
--   - encoding: g(i) = inf_{g∈∂f(δ(i))} g, g(i−1) = sup_{g∈∂f(δ(i−1))} g → IsLeast (superdiff dom f (δ i)) (g i), IsGreatest (superdiff dom f (δ (i-1))) (g (i-1)); reason: g(i) ∈ ∂f(δ(i)) and g(i−1) ∈ ∂f(δ(i−1)), so equality with the inf (sup) is being the least (greatest) element
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.1, p.6 (proof in Appendix A, p.27); p.7: "Lemmas 3.1 and 3.3 also hold for Algorithm 1"

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_IsDeltaStar
import Definitions.Def_AccelNewtonDinkelbach_RelaxedStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **Lemma 3.1: monotonicity of the iterates, values and supergradients.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.1, p.6 (proof p.27): "For every iteration
i ≥ 2, we have δ∗ ≤ δ(i) < δ(i−1), f(δ∗) ≥ f(δ(i)) > f(δ(i−1)) and g(i) ≥ g(i−1), where the last
inequality holds at equality if and only if g(i) = inf_{g∈∂f(δ(i))} g, g(i−1) = sup_{g∈∂f(δ(i−1))} g
and f(δ(i)) = 0. Moreover, f(δ(i))/f(δ(i−1)) + g(i)/g(i−1) ≤ 1."

For every proper concave `f` (encoded as `(dom, f)`), every `δ*` as in `IsDeltaStar`, every run of
relaxed steps and every `2 ≤ i ≤ N`:

1. `δ* ≤ δ(i) < δ(i−1)`;
2. `f(δ(i−1)) < f(δ(i)) ≤ f(δ*)`;
3. `g(i−1) ≤ g(i)`, with equality iff `g(i)` is the least element of `∂f(δ(i))`, `g(i−1)` is the
   greatest element of `∂f(δ(i−1))`, and `f(δ(i)) = 0`;
4. `f(δ(i))/f(δ(i−1)) + g(i)/g(i−1) ≤ 1`.

**Formalization Note** "`g(i) = inf_{g∈∂f(δ(i))} g`" is written `IsLeast (∂f(δ(i))) (g(i))`, which is
equivalent because `g(i) ∈ ∂f(δ(i))`; likewise `sup` is `IsGreatest`. No real `sInf`/`sSup` is used.
The divisions are by `f(δ(i−1)) < 0` and `g(i−1) < 0` (the run invariant). Relaxed runs include the
standard method of p.6 and Algorithm 1 (p.7: "Lemmas 3.1 and 3.3 also hold for Algorithm 1"). -/
theorem lemma_3_1_monotonicity (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δstar : ℝ) (hstar : IsDeltaStar dom f δstar)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (RelaxedStep dom f) dom f δ g N)
    (i : ℕ) (hi : 2 ≤ i) (hiN : i ≤ N) :
    (δstar ≤ δ i ∧ δ i < δ (i - 1)) ∧
      (f (δ i) ≤ f δstar ∧ f (δ (i - 1)) < f (δ i)) ∧
      g (i - 1) ≤ g i ∧
      (g i = g (i - 1) ↔
        IsLeast (superdiff dom f (δ i)) (g i) ∧
          IsGreatest (superdiff dom f (δ (i - 1))) (g (i - 1)) ∧ f (δ i) = 0) ∧
      f (δ i) / f (δ (i - 1)) + g i / g (i - 1) ≤ 1 := by sorry

end AccelNewtonDinkelbach
