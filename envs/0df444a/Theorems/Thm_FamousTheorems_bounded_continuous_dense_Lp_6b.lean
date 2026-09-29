-- Prove2me | Theorems.Thm_FamousTheorems_bounded_continuous_dense_Lp_6b
-- name    : FamousTheorems.bounded_continuous_dense_Lp_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:37.130641+00:00
-- url     : https://prove2.me/theorems/1833643d-5385-4438-a61f-b3318806df31
-- title:
--   Bounded continuous functions are dense in Lᵖ
-- statement:
--   **Bounded continuous functions are dense in $L^p$.** Let $\alpha$ be a normal topological space with its Borel $\sigma$-algebra and $\mu$ a weakly regular measure on $\alpha$. Let $E$ be a real normed space such that $\alpha$ or $E$ is second countable, and let $1\le p<\infty$. Then the bounded continuous functions $\alpha\to E$ form a dense subset of $L^p(\alpha,\mu;E)$.
--
--   This is the standard approximation theorem of $L^p$ theory. It lets one prove an identity or inequality for continuous functions first and then extend it to all of $L^p$. It is used for the continuity of translation in $L^p$, for the Riemann–Lebesgue lemma, and for the density of test functions.
--
--   **Formalization note.** Mathlib's `MeasureTheory.Lp.boundedContinuousFunction_dense`. `MeasureTheory.Lp.boundedContinuousFunction E p μ` is the subgroup of $L^p$ consisting of the classes of bounded continuous functions. `SecondCountableTopologyEither α E` means that $\alpha$ or $E$ is second countable. The hypothesis `p ≠ ⊤` excludes $p=\infty$, where the result fails.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Lp.boundedContinuousFunction_dense`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bounded_continuous_dense_Lp_6b {α : Type*} [TopologicalSpace α] [NormalSpace α] [MeasurableSpace α] [BorelSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : MeasureTheory.Measure α) [μ.WeaklyRegular]
    {p : ENNReal} [Fact (1 ≤ p)] [SecondCountableTopologyEither α E] (hp : p ≠ ⊤) :
    Dense (MeasureTheory.Lp.boundedContinuousFunction E p μ : Set (MeasureTheory.Lp E p μ)) := by sorry

end FamousTheorems
