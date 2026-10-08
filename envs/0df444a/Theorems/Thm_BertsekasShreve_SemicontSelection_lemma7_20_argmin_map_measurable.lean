-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_lemma7_20_argmin_map_measurable
-- name    : BertsekasShreve.SemicontSelection.lemma7_20_argmin_map_measurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:30.523905+00:00
-- url     : https://prove2.me/theorems/82ea2636-bbe8-459b-ae72-860f992fe826
-- title:
--   Lemma 7.20 — the argmin map $x\mapsto\{y: f(x,y)\le f^*(x)\}$ is Borel-measurable into $2^Y$
-- statement:
--   Let $X$ be a metrizable space, $Y$ a nonempty compact metric space, and $f:X\times Y\to R^*$ lower semicontinuous. Let $f^*(x)=\min_{y\in Y}f(x,y)$ and
--
--   $$F^*(x)=\{y\in Y\mid f(x,y)\le f^*(x)\}\qquad(x\in X).$$
--
--   Then each $F^*(x)$ is a closed subset of $Y$, and the map $F^*:X\to 2^Y$ is Borel-measurable, where $2^Y$ is the space of closed subsets of $Y$ with the topology of the Hausdorff metric.
--
--   The set $F^*(x)$ is the set of minimizers of $f(x,\cdot)$. Its measurable dependence on $x$ is what allows a minimizer to be chosen measurably, by composing $F^*$ with the selector of Lemma 7.18; this is the core of Proposition 7.33.
--
--   **Formalization Note** $2^Y$ is Mathlib's `Closeds Y` with the Hausdorff extended metric and its Borel σ-algebra. Mathlib puts the empty set at distance $\infty$ from every nonempty set, where the book's Definition C.1 uses $\operatorname{diam}Y$; in both topologies $\emptyset$ is an isolated point (as in the exponential topology of Appendix C), and on nonempty sets the two metrics coincide, so the Borel σ-algebras agree. The minimum $f^*(x)$ is written as the infimum $\inf_{y}f(x,y)$, which it equals (Proposition 7.32(a)) for nonempty compact $Y$. Nonemptiness is explicit because the source writes a minimum. The theorem asserts the existence of a map into `Closeds Y` whose value at $x$ is the set $F^*(x)$ — that is, closedness of each $F^*(x)$ — together with its measurability.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 152, Lemma 7.20 (Eq. (64) of Chapter 7); Appendix C, p. 303

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.20 (Bertsekas & Shreve, p. 152). Let `X` be metrizable, `Y` a nonempty compact metric space,
`f : X × Y → R*` lower semicontinuous, `f*(x) = min_{y ∈ Y} f(x, y)`, and
`F*(x) = {y ∈ Y | f(x, y) ≤ f*(x)}` (Eq. (64) of Chapter 7). Then `F* : X → 2^Y` is
Borel-measurable, where `2^Y` is the space of closed subsets of `Y` with the Hausdorff-metric
topology and its Borel σ-algebra. The statement asserts that each `F*(x)` is a closed set (so `F*`
is a map into `2^Y`) and that this map is Borel-measurable. -/
theorem lemma7_20_argmin_map_measurable {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (f : X × Y → EReal) (hf : LowerSemicontinuous f) :
    ∃ F : X → Closeds Y, (∀ x, (F x : Set Y) = {y | f (x, y) ≤ ⨅ y', f (x, y')}) ∧
      @Measurable _ _ (borel X) (borel (Closeds Y)) F := by sorry

end BertsekasShreve.SemicontSelection
