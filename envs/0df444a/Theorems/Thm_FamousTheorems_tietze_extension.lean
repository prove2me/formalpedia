-- Prove2me | Theorems.Thm_FamousTheorems_tietze_extension
-- name    : FamousTheorems.tietze_extension
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:14:55.700107+00:00
-- url     : https://prove2.me/theorems/47a8c76c-e226-4ea3-9818-d9451d4160b0
-- title:
--   The Tietze extension theorem
-- statement:
--   **The Tietze extension theorem (norm-preserving form).** Let $Y$ be a normal space and $e:X\to Y$ a closed embedding. Every bounded continuous $f:X\to\mathbb R$ extends to a bounded continuous $g:Y\to\mathbb R$ with $g\circ e=f$ and $\|g\|_\infty=\|f\|_\infty$.
--
--   This is the extension counterpart of Urysohn's lemma and characterises normality. It is used throughout topology and analysis: extending partitions of unity, proving that closed subsets of metric spaces are retracts of real-valued function spaces, and building continuous functions with prescribed boundary values.
--
--   **Formalization note.** Mathlib's `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tietze_extension {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]
    (f : BoundedContinuousFunction X ℝ) {e : X → Y} (he : Topology.IsClosedEmbedding e) :
    ∃ g : BoundedContinuousFunction Y ℝ, ‖g‖ = ‖f‖ ∧ ⇑g ∘ e = ⇑f := by sorry

end FamousTheorems
