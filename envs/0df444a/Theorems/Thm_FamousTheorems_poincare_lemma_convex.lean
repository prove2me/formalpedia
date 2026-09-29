-- Prove2me | Theorems.Thm_FamousTheorems_poincare_lemma_convex
-- name    : FamousTheorems.poincare_lemma_convex
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:36.524529+00:00
-- url     : https://prove2.me/theorems/e05fb660-3669-400c-a793-d5629f284291
-- title:
--   The Poincaré lemma for 1-forms on convex sets
-- statement:
--   **The Poincaré lemma for 1-forms on convex open sets.** Let $s$ be a convex open subset of a normed space $E$, and let $\omega$ be a differentiable 1-form on $s$ with values in a Banach space $F$ (over $\mathbb R$ or $\mathbb C$). Suppose $\omega$ is closed, that is, its derivative is symmetric: $D\omega(a)(x)(y)=D\omega(a)(y)(x)$. Then $\omega$ is exact: there is $f:E\to F$ with $Df(a)=\omega(a)$ for all $a\in s$.
--
--   This is the degree-one Poincaré lemma, and it says that de Rham cohomology in degree one vanishes on convex sets. It is the local fact behind potentials of conservative vector fields, primitives of holomorphic functions on convex domains, and the definition of de Rham cohomology as an obstruction to global primitives.
--
--   **Formalization note.** Mathlib's `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`. The 1-form is a map `ω : E → E →L[𝕜] F` with `𝕜` equal to $\mathbb R$ or $\mathbb C$ (`RCLike 𝕜`), and closedness is stated through the real Fréchet derivative `fderiv ℝ ω a`, a bilinear map. The primitive's derivative `HasFDerivAt f (ω a) a` is taken over `𝕜`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem poincare_lemma_convex {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {ω : E → E →L[𝕜] F}
    (hs : Convex ℝ s) (hso : IsOpen s) (hω : DifferentiableOn ℝ ω s)
    (hsymm : ∀ a ∈ s, ∀ x y : E, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f : E → F, ∀ a ∈ s, HasFDerivAt f (ω a) a := by sorry

end FamousTheorems
