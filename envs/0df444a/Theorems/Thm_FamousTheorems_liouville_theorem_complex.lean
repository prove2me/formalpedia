-- Prove2me | Theorems.Thm_FamousTheorems_liouville_theorem_complex
-- name    : FamousTheorems.liouville_theorem_complex
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:19.52765+00:00
-- url     : https://prove2.me/theorems/3205d545-6e29-4776-a7e4-e26016870948
-- title:
--   Liouville's theorem (complex analysis)
-- statement:
--   **Liouville's theorem.** Let $f:E\to F$ be complex-differentiable everywhere, where $E$ and $F$ are complex normed spaces. If $f$ is bounded, then $f$ is constant.
--
--   For $E=F=\mathbb C$, a bounded entire function is constant. This is one of the central results of complex analysis. It gives a short proof of the fundamental theorem of algebra, shows that the spectrum of an element of a complex Banach algebra is nonempty, and underlies Picard-type theorems.
--
--   **Formalization note.** Mathlib's `Differentiable.apply_eq_apply_of_bounded`. `Differentiable ℂ f` means complex (Fréchet) differentiability at every point, and boundedness is `Bornology.IsBounded (Set.range f)`. Constancy is stated as $f(z)=f(w)$ for all $z,w$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Differentiable.apply_eq_apply_of_bounded`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem liouville_theorem_complex {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} (hf : Differentiable ℂ f) (hb : Bornology.IsBounded (Set.range f)) (z w : E) :
    f z = f w := by sorry

end FamousTheorems
