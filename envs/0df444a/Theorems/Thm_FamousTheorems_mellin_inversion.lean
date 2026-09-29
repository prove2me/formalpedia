-- Prove2me | Theorems.Thm_FamousTheorems_mellin_inversion
-- name    : FamousTheorems.mellin_inversion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:17.559849+00:00
-- url     : https://prove2.me/theorems/cec1e8ad-3ce2-4417-8613-a3d98cfb12d1
-- title:
--   The Mellin inversion theorem
-- statement:
--   **The Mellin inversion theorem.** Let $f:(0,\infty)\to E$ (a complex Banach space). Suppose its Mellin transform $\mathcal Mf(s)=\int_0^\infty x^{s-1}f(x)\,dx$ converges on the line $\Re s=\sigma$ and is integrable along it, and $f$ is continuous at $x>0$. Then
--   $$f(x)=\frac1{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}x^{-s}\,\mathcal Mf(s)\,ds .$$
--
--   Mellin inversion is the multiplicative-group form of Fourier inversion. It is the basic tool of analytic number theory (Perron's formula, the explicit formulae) and of asymptotic analysis of Dirichlet series and integrals.
--
--   **Formalization note.** Mathlib's `mellinInv_mellin_eq`; `mellinInv σ F x` is the inverse Mellin integral along $\Re s=\sigma$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `mellinInv_mellin_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mellin_inversion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (σ : ℝ) (f : ℝ → E) {x : ℝ}
    (hx : 0 < x) (hf : MellinConvergent f (σ : ℂ))
    (hFf : Complex.VerticalIntegrable (mellin f) σ MeasureTheory.volume) (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by sorry

end FamousTheorems
