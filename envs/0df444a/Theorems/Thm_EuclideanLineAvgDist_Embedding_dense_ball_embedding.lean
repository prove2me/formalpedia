-- Prove2me | Theorems.Thm_EuclideanLineAvgDist_Embedding_dense_ball_embedding
-- name    : EuclideanLineAvgDist.Embedding.dense_ball_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:10.770384+00:00
-- url     : https://prove2.me/theorems/01300eb0-b63d-47da-a513-5f508040af78
-- title:
--   Lemma 1.7 — distance to a dense ball is a non-expansive embedding with bounded average distortion
-- statement:
--   Let $(X,d)$ be a finite metric space with $n$ points and $\Delta=\frac1{n^2}\sum_{x,y\in X}d(x,y)$. Let $\kappa>0$ and $c>2$. Suppose some $x^*\in X$ satisfies
--   $$|B(x^*,\Delta/c)|\ge\kappa n,$$
--   where $B(x,r)=\{y\in X:d(x,y)<r\}$. Then the map $f(x)=d\bigl(x,B(x^*,\Delta/c)\bigr)$ is non-expansive, and
--   $$\sum_{x,y\in X}d(x,y)\;\le\;\frac{1}{\frac{\kappa}{2}\bigl(1-\frac2c\bigr)}\sum_{x,y\in X}|f(x)-f(y)|,$$
--   that is, $\operatorname{avd}(f)\le 1/\bigl(\frac\kappa2(1-\frac2c)\bigr)$.
--
--   This is the "dense" case of the proof of Theorem 1.1: with $\kappa=1/64$ and $c=4$ it gives distortion at most $256$.
--
--   **Formalization Note** The finite metric space is a type with a `MetricSpace` and a `Fintype` instance; $n$ is its cardinality. The hypothesis makes the ball nonempty, so $f$ is a genuine minimum of distances.
--
--   Differences from the source:
--   - reading: $B(x^*,\Delta/c)$, open or closed not specified → the open ball $\{y: d(x^*,y)<\Delta/c\}$; reason: the source does not fix the convention; the open ball is used consistently throughout the mission (Corollary 2.2 uses the same ball)
--   - encoding: $\operatorname{avd}(f)\le 1/(\frac\kappa2(1-\frac2c))$ → $S_d\le \frac{1}{\frac\kappa2(1-\frac2c)}S_f$; reason: avoids the ratio; for $n\ge2$ the inequality forces $S_f>0$ and is equivalent to the ratio bound, and for $n=1$ both sums vanish (the ratio is $0/0$)
--   - encoding: a metric space $(X,d)$ with $n$ points → a finite type with a metric, $n$ its cardinality; reason: the source's sums and $n$ presuppose finiteness; same instances
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 5, Lemma 1.7

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

/-- Lemma 1.7 (p. 5). Let `(X,d)` be a finite metric space with `n = |X|` points and
`Δ = (1/n²) ∑_{x,y} d(x,y)`. Let `κ > 0` and `c > 2`. If some `x* ∈ X` has
`|B(x*, Δ/c)| ≥ κ n`, then `f(x) = d(x, B(x*, Δ/c))` is non-expansive and
`avd(f) ≤ 1 / ((κ/2)(1 - 2/c))`, stated cross-multiplied as
`∑_{x,y} d(x,y) ≤ (1 / ((κ/2)(1 - 2/c))) · ∑_{x,y} |f(x) - f(y)|`. Balls are open. -/
theorem dense_ball_embedding {X : Type*} [MetricSpace X] [Fintype X]
    (κ c : ℝ) (hκ : 0 < κ) (hc : 2 < c) (xstar : X)
    (hdense : κ * (Fintype.card X : ℝ) ≤ ((ball xstar (avgDist X / c)).card : ℝ)) :
    NonExpansive (distToFinset (ball xstar (avgDist X / c))) ∧
      distSum X ≤ (1 / ((κ / 2) * (1 - 2 / c))) *
        lineSpread (distToFinset (ball xstar (avgDist X / c))) := by sorry

end EuclideanLineAvgDist.Embedding
