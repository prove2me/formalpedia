-- Prove2me | Theorems.Thm_ChandrasekaranNullCone_clock_distance_5_7
-- name    : ChandrasekaranNullCone.clock_distance_5_7
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-26T15:34:47.911098+00:00
-- url     : https://prove2.me/theorems/ac5e009c-8cef-444c-83ed-3595e1a534fb
-- title:
--   Distance from the clock-damped state, eq. (5.7)
-- statement:
--   By the spectral theorem, the positive self-adjoint clock operator at fixed focusing cutoff (C.11) acts as multiplication by a measurable clock reading $u:X\to[0,\infty)$ on wavefunctions over a measure space $(X,\mu)$. Let $L>0$. Let $\omega\in L^2(\mu)$ be normalized, $\int_X|\omega|^2\,d\mu=1$; it is the wavefunction of $|\Omega_A\rangle$. Let $\psi_L=\frac{L}{L+u}\,\omega$ as in (5.6). Then
--   $$\|\omega-\psi_L\|^{2}\;\le\;1-\operatorname{Re}\langle\omega|\psi_L\rangle\;=\;\Big\langle\omega\Big|\frac{u}{L+u}\Big|\omega\Big\rangle=\int_X\frac{u}{L+u}\,|\omega|^{2}\,d\mu .$$
--
--   **Role in the source.** This bounds the distance from $|\Psi_L\rangle$ to $|\Omega_A\rangle$. The bound enters the triangle inequality (5.4) for the probability of a clock reading above $\ell(D)$.
--
--   **Formalization note.** The source writes $1-\langle\Omega_A|\Psi_L\rangle$; this inner product is real because $L/(L+u)\ge0$, and the Lean statement uses its real part. The source states (5.7) after taking $\Xi_*\to\infty$; this item is the fixed-cutoff inequality that the source integrates before that limit. The inner product is $\langle\omega|\psi\rangle=\int_X\overline{\omega}\,\psi\,d\mu$. The measure space and the reading $u\ge0$ are arbitrary, which covers any positive self-adjoint clock operator. Integrability of all integrands follows from $\omega\in L^2(\mu)$ (`MemLp ω 2 μ`).
-- source:
--   Chandrasekaran 2026, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924v1, §5.1, p. 36, eq. (5.7) at fixed focusing cutoff (the bound obtained by integrating [u/(L+u)]^2 <= u/(L+u) over the clock readings, (C.14)).

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
open MeasureTheory

namespace ChandrasekaranNullCone

/-- Chandrasekaran (arXiv:2611.34924), eq. (5.7) at fixed focusing cutoff, with the clock operator
in multiplication-operator form (spectral theorem): wavefunctions on a measure space `(X, μ)`,
clock reading `u : X → [0, ∞)`. For a normalized `ω ∈ L²(μ)` and `ψ_L = L/(L+u) · ω`,
`‖ω - ψ_L‖² ≤ 1 - Re⟨ω|ψ_L⟩ = ⟨ω| u/(L+u) |ω⟩`. -/
theorem clock_distance_5_7 {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (L : ℝ) (hL : 0 < L) (ω : X → ℂ)
    (hω : MemLp ω 2 μ) (hnorm : ∫ x, ‖ω x‖ ^ 2 ∂μ = 1) :
    let ψL : X → ℂ := fun x => ((L / (L + u x) : ℝ) : ℂ) * ω x
    (∫ x, ‖ω x - ψL x‖ ^ 2 ∂μ) ≤ 1 - (∫ x, star (ω x) * ψL x ∂μ).re ∧
      1 - (∫ x, star (ω x) * ψL x ∂μ).re = ∫ x, u x / (L + u x) * ‖ω x‖ ^ 2 ∂μ := by sorry

end ChandrasekaranNullCone
