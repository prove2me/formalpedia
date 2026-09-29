-- Prove2me | Theorems.Thm_FamousTheorems_mazur_ulam_theorem
-- name    : FamousTheorems.mazur_ulam_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:31.014625+00:00
-- url     : https://prove2.me/theorems/1003fc46-546e-4935-bf13-773df0991221
-- title:
--   The Mazur–Ulam theorem
-- statement:
--   **The Mazur–Ulam theorem.** Every surjective isometry between real normed affine spaces is affine.
--
--   Mazur and Ulam proved this in 1932. Over $\mathbb R$, the metric determines the linear structure up to translation: a distance-preserving bijection must preserve midpoints, and hence be affine. The statement fails over $\mathbb C$, where complex conjugation is an isometry that is not complex-linear.
--
--   **Formalization note.** Mathlib's `IsometryEquiv.toRealAffineIsometryEquiv` and `IsometryEquiv.coeFn_toRealAffineIsometryEquiv`. The statement says that the surjective isometry `f : PE ≃ᵢ PF` has the same underlying function as some real affine isometric equivalence `PE ≃ᵃⁱ[ℝ] PF`. `PE` and `PF` are metric spaces that are affine torsors over real normed spaces $E$ and $F$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsometryEquiv.toRealAffineIsometryEquiv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mazur_ulam_theorem {E PE F PF : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace PE] [NormedAddTorsor E PE]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace PF] [NormedAddTorsor F PF] (f : PE ≃ᵢ PF) :
    ∃ g : PE ≃ᵃⁱ[ℝ] PF, ⇑g = ⇑f := by sorry

end FamousTheorems
