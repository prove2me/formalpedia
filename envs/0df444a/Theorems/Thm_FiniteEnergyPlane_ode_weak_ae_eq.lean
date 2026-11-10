-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ode_weak_ae_eq
-- name    : FiniteEnergyPlane.ode_weak_ae_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T22:23:44.455077+00:00
-- url     : https://prove2.me/theorems/52053fb4-bde4-4b5e-8f6a-23e0250d0966
-- title:
--   Weak solutions of a scalar first-order linear ODE on the line
-- statement:
--   Let $E$ be a real Banach space, $\Lambda : \mathbb{R} \to \mathbb{R}$ smooth, and $f : \mathbb{R} \to E$ locally integrable. Suppose $f$ is a weak solution of $f' + \Lambda' f = 0$, that is,
--   $$\int_{\mathbb{R}} \bigl(-\eta'(s) + \Lambda'(s)\,\eta(s)\bigr)\, f(s)\, ds = 0$$
--   for every smooth compactly supported $\eta : \mathbb{R} \to \mathbb{R}$. Then there is $C \in E$ with $f(s) = e^{-\Lambda(s)} C$ for almost every $s$.
--
--   **Role.** Identifies the weak solutions of a scalar first-order linear ODE with a smooth coefficient, for example the Fourier coefficients of a kernel element of a Cauchy-Riemann type operator on the cylinder.
-- source:
--   Standard distribution theory; Lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

/-- A locally integrable `f : ℝ → E` that weakly solves `f' + Λ' f = 0`, i.e.
`∫ (-η' + Λ' η) • f = 0` for every smooth compactly supported `η`, equals `e^{-Λ} • C` almost
everywhere for some constant `C`. -/
theorem ode_weak_ae_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Λ : ℝ → ℝ) (hΛ : ContDiff ℝ ∞ Λ) (f : ℝ → E)
    (hf : LocallyIntegrable f volume)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ s, (-deriv η s + deriv Λ s * η s) • f s = 0) :
    ∃ C : E, ∀ᵐ s, f s = Real.exp (-Λ s) • C := by
  sorry

end FiniteEnergyPlane
