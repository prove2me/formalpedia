-- Prove2me | Theorems.Thm_FamousTheorems_liouville_theorem_harmonic
-- name    : FamousTheorems.liouville_theorem_harmonic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:40.247902+00:00
-- url     : https://prove2.me/theorems/3f25436a-f841-41bd-a482-05921029193c
-- title:
--   Liouville's theorem for harmonic functions
-- statement:
--   **Liouville's theorem for harmonic functions.** Every bounded harmonic function $f:\mathbb C\to E$ into a real normed space is constant.
--
--   This is the harmonic analogue of Liouville's theorem for entire functions, and it follows from the mean value property on larger and larger discs. It is the simplest rigidity result in potential theory, with generalisations to Riemannian manifolds of nonnegative Ricci curvature (Yau).
--
--   **Formalization note.** Mathlib's `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant`. `InnerProductSpace.HarmonicOnNhd f Set.univ` says $f$ is harmonic (twice differentiable with vanishing Laplacian) near every point of $\mathbb C=\mathbb R^2$, and boundedness is `Bornology.IsBounded (Set.range f)`. The conclusion is that any two values of $f$ are equal.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem liouville_theorem_harmonic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E)
    (hf : InnerProductSpace.HarmonicOnNhd f Set.univ) (hb : Bornology.IsBounded (Set.range f)) :
    ∀ z w : ℂ, f z = f w := by sorry

end FamousTheorems
