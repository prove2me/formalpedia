-- Prove2me | Theorems.Thm_ChandrasekaranNullCone_clock_minimizer_5_5
-- name    : ChandrasekaranNullCone.clock_minimizer_5_5
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-26T15:33:35.282391+00:00
-- url     : https://prove2.me/theorems/1768408b-e2cd-5b48-aa99-d261ee25808b
-- title:
--   The damped clock wavefunction minimizes the regularized functional, eqs. (5.5), (C.12)
-- statement:
--   The clock operator $\hat{\bar u}_*(\Xi_*)$ at fixed focusing cutoff is positive and self-adjoint (C.11). By the spectral theorem it acts, in a suitable representation, as multiplication by a measurable clock reading $u:X\to[0,\infty)$ on wavefunctions over a measure space $(X,\mu)$. The source puts this as "at each reading $u$ the second term weights $|\langle u|\Psi\rangle|^2$ by $u/L$". Let $L>0$, let $\omega$ be the wavefunction of $|\Omega_A\rangle$, and define the functional (5.5)
--   $$\mathcal F[\psi]=\int_X|\psi-\omega|^2\,d\mu+\frac1L\int_X u\,|\psi|^2\,d\mu\ \in[0,\infty].$$
--   The solution of the stationarity equation (C.12), $(1+u/L)\,\psi_L=\omega$, is
--   $$\psi_L=\frac{L}{L+u}\,\omega .$$
--   It satisfies $\mathcal F[\psi_L]\le\mathcal F[\psi]$ for every (almost-everywhere measurable) wavefunction $\psi$, so $\psi_L$ minimizes (5.5).
--
--   **Role in the source.** This constructs the state $|\Psi_L\rangle$ close to $|\Omega_A\rangle$ with finite clock expectation. The bound on the probability of a clock reading above $\ell(D)$ (5.4) is built on it.
--
--   **Formalization note.** The measure space $(X,\mu)$ and the measurable reading $u\ge0$ are arbitrary. This covers any positive self-adjoint clock operator, bounded or not, with any multiplicity; clock readings in $[0,\infty)$ with Lebesgue measure are the special case $X=[0,\infty)$, $u=\mathrm{id}$. The functional takes values in $[0,\infty]$ (`ENNReal` lower integrals), so no integrability assumptions are needed and $\mathcal F[\psi]=\infty$ is allowed. Measurability of $\omega$ and $\psi$ is assumed. The source then removes the cutoff ($\Xi_*\to\infty$, (5.6)); the statement here is the fixed-cutoff minimization (5.5)/(C.12) that this limit starts from.
-- source:
--   Chandrasekaran 2026, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924v1, §5.1, p. 35, eq. (5.5), the stationarity condition (C.12) quoted in the text, and the minimizer (5.6) at fixed focusing cutoff.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
open MeasureTheory

namespace ChandrasekaranNullCone

/-- Chandrasekaran (arXiv:2611.34924), eqs. (5.5) and (C.12), with the clock operator at fixed
focusing cutoff in multiplication-operator form (spectral theorem): wavefunctions on a measure
space `(X, μ)`, clock reading `u : X → [0, ∞)`. The wavefunction `ψ_L = L/(L+u) · ω`, i.e. the
solution of `(1 + u/L) ψ_L = ω`, minimizes `‖ψ - ω‖² + ⟨ψ|ū|ψ⟩/L` over all (a.e.-measurable)
wavefunctions `ψ`. -/
theorem clock_minimizer_5_5 {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (L : ℝ) (hL : 0 < L) (ω ψ : X → ℂ)
    (hω : AEMeasurable ω μ) (hψ : AEMeasurable ψ μ) :
    let ψL : X → ℂ := fun x => ((L / (L + u x) : ℝ) : ℂ) * ω x
    let F : (X → ℂ) → ENNReal := fun φ =>
      (∫⁻ x, ‖φ x - ω x‖ₑ ^ 2 ∂μ) + ENNReal.ofReal (1 / L) * ∫⁻ x, ENNReal.ofReal (u x) * ‖φ x‖ₑ ^ 2 ∂μ
    F ψL ≤ F ψ := by sorry

end ChandrasekaranNullCone
