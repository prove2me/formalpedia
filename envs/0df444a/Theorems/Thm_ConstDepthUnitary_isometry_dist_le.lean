-- Prove2me | Theorems.Thm_ConstDepthUnitary_isometry_dist_le
-- name    : ConstDepthUnitary.isometry_dist_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:51.535197+00:00
-- url     : https://prove2.me/theorems/b579b136-4615-4940-86ed-0335b1283f11
-- title:
--   Lemma 3.3 — distance of isometries and rescaling
-- statement:
--   Let $V,W$ be isometries from a Hilbert space $H_1$ to a Hilbert space $H_2$, and let $\beta>0$. Then
--   $$\|V-W\|\le\frac2{1+\beta}\|V-\beta W\|.$$
--   The lemma compares two isometries when one of them is known only up to a positive scalar.
--
--   Differences from the source:
--   - encoding: isometries from Hilbert space H1 to H2 → ℂ-linear isometries between complete complex inner product spaces, with the operator norm; reason: the Lean rendering of the same objects
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.3, p.18

import Mathlib

namespace ConstDepthUnitary

/-- Lemma 3.3: for isometries `V, W` between Hilbert spaces and `β > 0`,
`‖V − W‖ ≤ 2/(1+β) ‖V − βW‖`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.3, p.18.

**Formalization Note** The Hilbert spaces are complex and complete, and `V, W` are linear isometries; the norm is the
operator norm. The matrices of the mission, as maps between finite-dimensional `EuclideanSpace`s, are a special case. -/
theorem isometry_dist_le {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (V W : H₁ →ₗᵢ[ℂ] H₂) (β : ℝ) (hβ : 0 < β) :
    ‖V.toContinuousLinearMap - W.toContinuousLinearMap‖ ≤
      2 / (1 + β) * ‖V.toContinuousLinearMap - (β : ℂ) • W.toContinuousLinearMap‖ := by sorry

end ConstDepthUnitary
