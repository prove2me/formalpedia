-- Prove2me | Theorems.Thm_FiniteEnergyPlane_monotoneOn_energy_ratio
-- name    : FiniteEnergyPlane.monotoneOn_energy_ratio
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:53:01.994021+00:00
-- url     : https://prove2.me/theorems/634868bd-706b-4f0c-b36a-4445c5117a0c
-- title:
--   Monotone energy ratio for maps $\partial_t u=A\,\partial_s u$ with $A$ close to a complex structure
-- statement:
--   Let $F$ be a real inner product space and $J_0:F\to F$ a continuous linear map with $J_0^2=-1$ and $\|J_0\|\le b$, where $b\ge1$. Put $\gamma=1+b^2$ and $g(v,v')=\langle v,v'\rangle+\langle J_0v,J_0v'\rangle$. Let $\Lambda\ge0$ and $S>0$ with $\Lambda S\le 1/(4\gamma^2b)$, let $q\in F$, $U\subseteq\mathbb C$ open and $u:\mathbb C\to F$ of class $C^2$ on $U$. Assume that at every $z\in U$ with $\|u(z)-q\|<S$ one has $\partial_tu(z)=A(z)\,\partial_su(z)$ and $\|A(z)-J_0\|\le\Lambda\|u(z)-q\|$, and that the sets $\{z\in U:\|u(z)-q\|\le\rho\}$ are compact for every $\rho<S$.
--
--   Let $\varphi:\mathbb R\to[0,1]$ be $C^1$, nonincreasing, with $\varphi=0$ on $[3/4,\infty)$, $\varphi'=0$ on $(3/4,\infty)$ and $\varphi'$ bounded. For $0<s<S$ set
--   $$\Phi_s(z)=\mathbf 1_U(z)\,\varphi\!\left(\frac{g(u(z)-q,\,u(z)-q)}{s^2}\right) g\bigl(J_0\partial_su(z),\,\partial_tu(z)\bigr).$$
--   Then each $\Phi_s$ is integrable and nonnegative, and with $C=(\gamma b+2\gamma^2b)\Lambda$ the function
--   $$s\mapsto \frac{e^{2Cs}}{s^2}\int_{\mathbb C}\Phi_s$$
--   is nondecreasing on $(0,S)$.
--
--   **Role.** This is the monotone quantity behind the monotonicity lemma for pseudoholomorphic curves, stated for a model map into a vector space, where the almost complex structure along $u$ is only close to the constant structure $J_0$.
--
--   **Formalization Note.** $\partial_s u=Du(z)\,1$, $\partial_t u=Du(z)\,i$; the integrals are Bochner integrals over $\mathbb C$ for Lebesgue measure; the function $\Phi_s$ is written out with `Set.indicator` and the inner product.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Monotone energy ratio near a complex structure. Let `J₀` be a complex structure on a real inner
product space with `‖J₀‖ ≤ b`, `1 ≤ b`, `γ = 1 + b²`, and `g(v, v') = ⟪v, v'⟫ + ⟪J₀ v, J₀ v'⟫`. Let
`Λ ≥ 0`, `S > 0` with `Λ S ≤ 1 / (4 γ² b)`, `U ⊆ ℂ` open, `u` a `C²` map on `U` with
`∂ₜu = A(z) ∂ₛu` and `‖A(z) - J₀‖ ≤ Λ ‖u z - q‖` wherever `‖u z - q‖ < S`, and with compact sets
`{z ∈ U | ‖u z - q‖ ≤ ρ}` for `ρ < S`. Let `φ` be a nonincreasing `C¹` cutoff in `[0, 1]`
vanishing on `[3/4, ∞)` with bounded derivative vanishing on `(3/4, ∞)`. Put
`Φ_s(z) = 1_U(z) φ(g(u z - q, u z - q) / s²) g(J₀ ∂ₛu, ∂ₜu)`. Then for `0 < s < S`, `Φ_s` is
integrable and nonnegative, and `s ↦ e^{2 C s} ∫ Φ_s / s²` is nondecreasing on `(0, S)`, where
`C = (γ b + 2 γ² b) Λ`. -/
theorem monotoneOn_energy_ratio {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J₀ : F →L[ℝ] F) (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ F) {b : ℝ} (hb1 : 1 ≤ b)
    (hJb : ‖J₀‖ ≤ b) {Λ S : ℝ} (hΛ : 0 ≤ Λ) (hS : 0 < S)
    (hΛS : Λ * S ≤ 1 / (4 * (1 + b ^ 2) ^ 2 * b)) (q : F) {U : Set ℂ} {u : ℂ → F}
    (A : ℂ → F →L[ℝ] F) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hhol : ∀ z ∈ U, ‖u z - q‖ < S → fderiv ℝ u z Complex.I = A z (fderiv ℝ u z 1) ∧
      ‖A z - J₀‖ ≤ Λ * ‖u z - q‖)
    (hprop : ∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ})
    {φ : ℝ → ℝ} (hφc : ContDiff ℝ 1 φ) (hφ0 : ∀ t, 3 / 4 ≤ t → φ t = 0)
    (hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (hφd : ∀ t, deriv φ t ≤ 0)
    (hφd0 : ∀ t, 3 / 4 < t → deriv φ t = 0) {Mφ : ℝ} (hMφ : ∀ t, |deriv φ t| ≤ Mφ) :
    (∀ s ∈ Ioo 0 S, Integrable (fun z => U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) ∧ ∀ z, 0 ≤ U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) ∧
    MonotoneOn (fun s => Real.exp (2 * (((1 + b ^ 2) * b + 2 * (1 + b ^ 2) ^ 2 * b) * Λ) * s) *
      (∫ z, U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) / s ^ 2) (Ioo 0 S) := by
  sorry

end FiniteEnergyPlane
