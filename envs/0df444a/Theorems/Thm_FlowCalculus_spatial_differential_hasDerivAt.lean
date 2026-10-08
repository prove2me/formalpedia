-- Prove2me | Theorems.Thm_FlowCalculus_spatial_differential_hasDerivAt
-- name    : FlowCalculus.spatial_differential_hasDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T14:46:21.556993+00:00
-- url     : https://prove2.me/theorems/7008c7cb-6a2f-40da-8647-287f175bcbd9
-- title:
--   First variational equation for the spatial differential of a smooth time-dependent flow
-- statement:
--   Let $E$ be a real Banach space and let $X,\psi:\mathbb R\times E\to E$ be jointly smooth. Assume the flow equation $\partial_t\psi(t,y)=X(t,\psi(t,y))$ for every time and point. Then for every $t,y,v$,
--   $$\frac{d}{ds}\Big|_{s=t}\big(D_y\psi(s,y)v\big)=D_xX(t,\psi(t,y))\big(D_y\psi(t,y)v\big).$$
--   No initial condition or invertibility assumption is needed for this differential identity. It is the first variational equation: differentiating the flow equation in the initial spatial variable and interchanging the mixed derivatives gives the stated result. In Geiges' Lemma 2.19 it accounts for the change of the tangent vector used to evaluate the pulled-back one-form.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry II (2006), https://arxiv.org/abs/math/0307242, Lemma 2.19, pp. 13–14. This is the Banach-space coordinate-calculus ingredient of the one-form identity, rather than an additional theorem stated verbatim in the source.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped ContDiff

theorem FlowCalculus.spatial_differential_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (X : ℝ → E → E) (hX : ContDiff ℝ ∞ (fun p : ℝ × E => X p.1 p.2))
    (ψ : ℝ → E → E) (hψ : ContDiff ℝ ∞ (fun p : ℝ × E => ψ p.1 p.2))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (t : ℝ) (y v : E) :
    HasDerivAt (fun s => fderiv ℝ (ψ s) y v)
      (fderiv ℝ (X t) (ψ t y) (fderiv ℝ (ψ t) y v)) t := by sorry
