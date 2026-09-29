-- Prove2me | Theorems.Thm_FamousTheorems_jacobi_identity_vector_fields
-- name    : FamousTheorems.jacobi_identity_vector_fields
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:29.201985+00:00
-- url     : https://prove2.me/theorems/f1df2ad4-a71b-4872-9c3d-8f0c58056a8f
-- title:
--   The Jacobi identity for the Lie bracket of vector fields on a manifold
-- statement:
--   **The Jacobi identity for vector fields.** Let $M$ be a manifold and $U,V,W$ vector fields on $M$ of sufficient smoothness ($C^2$ for real manifolds, analytic in general). The Lie bracket of vector fields satisfies
--   $$[U,[V,W]]=[[U,V],W]+[V,[U,W]] .$$
--
--   Together with antisymmetry, this makes the smooth vector fields on a manifold into a Lie algebra, the infinite-dimensional Lie algebra of the diffeomorphism group. Restricted to left-invariant vector fields, it gives the Lie algebra of a Lie group.
--
--   **Formalization note.** Mathlib's `VectorField.leibniz_identity_mlieBracket`, where the identity is written in its Leibniz form, which is equivalent to the Jacobi form by antisymmetry. `VectorField.mlieBracket I V W` is the Lie bracket for the model with corners `I`. The smoothness `minSmoothness 𝕜 2` is $C^2$ over $\mathbb R$ or $\mathbb C$ and analytic ($C^\omega$) over other fields, and the manifold is assumed of class `minSmoothness 𝕜 3`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `VectorField.leibniz_identity_mlieBracket`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobi_identity_vector_fields {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (minSmoothness 𝕜 3) M] {U V W : (x : M) → TangentSpace I x}
    (hU : ContMDiff I I.tangent (minSmoothness 𝕜 2) fun x => (⟨x, U x⟩ : TangentBundle I M))
    (hV : ContMDiff I I.tangent (minSmoothness 𝕜 2) fun x => (⟨x, V x⟩ : TangentBundle I M))
    (hW : ContMDiff I I.tangent (minSmoothness 𝕜 2) fun x => (⟨x, W x⟩ : TangentBundle I M)) :
    VectorField.mlieBracket I U (VectorField.mlieBracket I V W) =
      VectorField.mlieBracket I (VectorField.mlieBracket I U V) W + VectorField.mlieBracket I V (VectorField.mlieBracket I U W) := by sorry

end FamousTheorems
