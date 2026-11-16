-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_lemma_6_2
-- name    : BourgainUnion.Euclidean.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:36:54.323202+00:00
-- url     : https://prove2.me/theorems/650894ef-cd15-4e82-9a42-4820c5d57541
-- title:
--   Lemma 6.2 — (22) is a metric and $A$ is 1-strongly Euclidean
-- statement:
--   For every integer $m\ge1$ and every real $r>0$, the distance (22) on the two-layer cube $X_m=A\cup B$ is a metric: it vanishes exactly on the diagonal, is nonnegative and symmetric, and satisfies the triangle inequality. Moreover $A$ is 1-strongly Euclidean in $X_m$: $A$ and $A\cup\{x\}$, for every $x\in X_m$, embed isometrically into $\ell_2$.
--
--   Differences from the source:
--   - encoding: X_m = A ∪ B, two copies of {0,1}^m → Bool × (Fin m → Bool), with a_x = (false, x) and b_x = (true, x); reason: a relabeling of the points
--   - encoding: (22) defines a metric on X_m → the raw distance satisfies the published IsPseudometric and separates points; reason: these are exactly the metric axioms
--   - encoding: A is 1-strongly Euclidean in X_m → RawEuclidean of A and of A ∪ {x} for every x, for the raw distance (22); reason: this is OneStrong for the metric (22), stated without installing a metric instance before the metric axioms are proved
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 26, §6.1, Lemma 6.2, equation (22)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel
import Definitions.Def_BourgainUnion_Euclidean_Supplement_CubeModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Lemma 6.2, p. 26: (22) is a metric on `X_m` and `A` is 1-strongly Euclidean in it, stated
for the raw distance (no metric instance is assumed). -/
theorem lemma_6_2 (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (hr : 0 < r) :
    GeometryOfGraphs.FlowCut.IsPseudometric (cubeDist m r) ∧
    (∀ x y, cubeDist m r x y = 0 → x = y) ∧
    RawEuclidean (cubeDist m r) (layerA m) ∧
    ∀ x : Cube m, RawEuclidean (cubeDist m r) (layerA m ∪ {x}) := by sorry

end BourgainUnion.Euclidean.Supplement
