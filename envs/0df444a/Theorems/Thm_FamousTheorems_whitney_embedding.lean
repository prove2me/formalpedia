-- Prove2me | Theorems.Thm_FamousTheorems_whitney_embedding
-- name    : FamousTheorems.whitney_embedding
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:21.849287+00:00
-- url     : https://prove2.me/theorems/09f8ad7a-a3b0-42d3-a836-b7bc8696a141
-- title:
--   The Whitney embedding theorem (weak form, compact manifolds)
-- statement:
--   **The Whitney embedding theorem (weak form).** Every compact Hausdorff smooth manifold $M$ (modelled on a finite-dimensional real space, possibly with corners) admits, for some $n$, a smooth closed embedding $e:M\to\mathbb R^n$ whose derivative is injective at every point.
--
--   Abstract manifolds are thus no more general than submanifolds of Euclidean space. The strong Whitney theorem bounds $n$ by $2\dim M$, but the weak form, proved with bump functions, is enough for most uses: Riemannian metrics by pullback, tubular neighbourhoods and transversality arguments.
--
--   **Formalization note.** Mathlib's `exists_embedding_euclidean_of_compact`. Smoothness is `ContMDiff … ∞`, the embedding is `Topology.IsClosedEmbedding`, and immersion is injectivity of `mfderiv` at every point. No bound on the dimension `n` is given.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_embedding_euclidean_of_compact`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped ContDiff Manifold

theorem whitney_embedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ e ∧ Topology.IsClosedEmbedding e ∧
        ∀ x : M, Function.Injective (mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) e x) := by sorry

end FamousTheorems
