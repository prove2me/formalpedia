-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_product_slit
-- name    : BirkhoffGlobalSection.ambient_rotation_product_slit
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:49:37.743387+00:00
-- url     : https://prove2.me/theorems/b429746c-af1d-4dd2-a611-52133627fe96
-- title:
--   Bounded defect of the ambient rotation under composition
-- statement:
--   Bounded defect of the ambient rotation under composition of symplectic maps.
--
--   Identify $\mathbb R^4$ with $\mathbb C^2$ through $z=q-ip$. For a real linear map $Y$, write $P(Y)$ for its complex-linear part and $d(Y)=\det_{\mathbb C}P(Y)$ for its ambient determinant. Let $\Phi$ and $M$ be symplectic, that is, they preserve $\omega(u,v)=u\cdot Jv$. Then
--
--   $$
--   d(\Phi M)\,\overline{d(\Phi)}\,\overline{d(M)}\ \notin\ (-\infty,0] .
--   $$
--
--   It follows that, for a continuous family $\Phi(t)$ of symplectic maps and a fixed symplectic $M$, continuous arguments of $d(\Phi(t)M)$ and of $d(\Phi(t))$ have increments that differ by less than $2\pi$.
--
--   This is the bounded-defect (quasimorphism) property of the determinant rotation map. It transfers rotation estimates for fundamental solutions to solutions with an arbitrary, possibly very large, symplectic initial value.
--
--   **Formalization Note** Symplecticity is stated as `Φ u ⬝ᵥ qI.mulVec (Φ v) = u ⬝ᵥ qI.mulVec v`. The ambient determinant is `ambientRotationDet`, and the conclusion is membership in `Complex.slitPlane`.
-- source:
--   Gutt, Generalized Conley--Zehnder index, https://arxiv.org/pdf/1307.7239, Corollary 12, Eq. (9), pp. 8-9 (rotation map via the determinant of the complex-linear part). Derived auxiliary claim: for symplectic maps the complex-linear parts satisfy P(Phi M) = P(Phi) P(M) + K(Phi) conj(K(M)), which gives the bounded defect; not a verbatim statement of the reference.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

/-- Bounded defect of the ambient rotation under composition. For symplectic
maps `Φ` and `M`, the ambient determinant of `Φ ∘ M` times the conjugates of
the ambient determinants of `Φ` and `M` never lies on the closed negative real
axis. Consequently continuous ambient angles of `t ↦ Φ(t) ∘ M` and of
`t ↦ Φ(t)` have increments differing by less than `2π`. -/
theorem ambient_rotation_product_slit (Φ M : Phase →L[ℝ] Phase)
    (hΦ : ∀ u v : Phase,
      Φ u ⬝ᵥ TangentialHessian.qI.mulVec (Φ v) = u ⬝ᵥ TangentialHessian.qI.mulVec v)
    (hM : ∀ u v : Phase,
      M u ⬝ᵥ TangentialHessian.qI.mulVec (M v) = u ⬝ᵥ TangentialHessian.qI.mulVec v) :
    ambientRotationDet (Φ.comp M) * (starRingEnd ℂ) (ambientRotationDet Φ) *
      (starRingEnd ℂ) (ambientRotationDet M) ∈ Complex.slitPlane := by sorry

end BirkhoffGlobalSection
