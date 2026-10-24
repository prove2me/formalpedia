-- Prove2me | Theorems.Thm_FiniteEnergyPlane_integral_mul_bilin_fderiv_eq
-- name    : FiniteEnergyPlane.integral_mul_bilin_fderiv_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:06:33.983678+00:00
-- url     : https://prove2.me/theorems/666ae1bf-3cfa-482a-828c-1fe6307b85da
-- title:
--   Integral of $\psi\,\sigma(\partial_s u,\partial_t u)$ for an antisymmetric bilinear form $\sigma$ and a compactly supported weight $\psi$
-- statement:
--   Let $F$ be a real normed space and $\sigma:F\times F\to\mathbb{R}$ a continuous bilinear form with $\sigma(v,w)=-\sigma(w,v)$. Let $U\subseteq\mathbb{C}$ be open, let $u:\mathbb{C}\to F$ be $C^2$ on $U$, let $q\in F$, and let $\psi:\mathbb{C}\to\mathbb{R}$ be $C^1$ with compact support contained in $U$. Writing $\partial_s f=Df\cdot1$ and $\partial_t f=Df\cdot i$,
--   $$\int_{\mathbb{C}}\psi\,\sigma(\partial_su,\partial_tu)\;=\;-\frac12\int_{\mathbb{C}}\Bigl(\partial_s\psi\;\sigma(u-q,\partial_tu)-\partial_t\psi\;\sigma(u-q,\partial_su)\Bigr).$$
--
--   For $F=\mathbb{R}^{2n}$ and $\sigma$ a symplectic form, the left side is $\int\psi\,u^*\sigma$, and the identity expresses it through first derivatives of $u$ and of the weight only.
--
--   **Formalization Note** $\sigma$ is `F →L[ℝ] F →L[ℝ] ℝ`; $u$ is `ContDiffOn ℝ 2 u U`, $\psi$ is `ContDiff ℝ 1 ψ` with `HasCompactSupport ψ` and `tsupport ψ ⊆ U`. Both integrals are Bochner integrals over $\mathbb{C}$ with Lebesgue measure; the integrands vanish outside $\operatorname{tsupport}\psi$.
-- source:
--   Standard (Stokes' theorem for an exact 2-form); used for the monotonicity lemma, A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff

/-- Let `σ` be an antisymmetric continuous bilinear form on `F`, `u` a `C²` map on an open set
`U ⊆ ℂ`, `q ∈ F`, and `ψ` a real `C¹` function with compact support in `U`. Writing
`∂ₛ = D(·) 1`, `∂ₜ = D(·) i`,
`∫ ψ σ(∂ₛu, ∂ₜu) = -½ ∫ (∂ₛψ σ(u - q, ∂ₜu) - ∂ₜψ σ(u - q, ∂ₛu))`. -/
theorem integral_mul_bilin_fderiv_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (σ : F →L[ℝ] F →L[ℝ] ℝ) (hσ : ∀ v w, σ v w = -σ w v) {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → F} (hu : ContDiffOn ℝ 2 u U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (q : F) :
    ∫ z, ψ z * σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) =
      -(1 / 2) * ∫ z, (fderiv ℝ ψ z 1 * σ (u z - q) (fderiv ℝ u z Complex.I) -
        fderiv ℝ ψ z Complex.I * σ (u z - q) (fderiv ℝ u z 1)) := by
  sorry

end FiniteEnergyPlane
