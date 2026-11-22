-- Prove2me | Theorems.Thm_ApproxIdentity_tendsto_schwartz_convolution_dilate
-- name    : ApproxIdentity.tendsto_schwartz_convolution_dilate
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:53.529732+00:00
-- url     : https://prove2.me/theorems/bc54d7e9-85d6-4786-86c5-32234e2ed67b
-- title:
--   Approximate identity in $\mathcal S(\mathbb R^n)$: $\varepsilon^{-n}\psi(\cdot/\varepsilon)*\varphi\to\varphi$ in $\mathcal S$ as $\varepsilon\to0^+$ when $\int\psi=1$
-- statement:
--   **Dilates of a Schwartz kernel with integral one form an approximate identity in $\mathcal S(\mathbb R^n)$.** Let $E$ be a finite-dimensional real inner product space of dimension $n$ (a copy of $\mathbb R^n$ with Lebesgue measure), let $\psi,\varphi\in\mathcal S(E)$ be complex-valued Schwartz functions with $\int_E\psi(x)\,dx=1$, and for $\varepsilon>0$ let
--   $$\psi_\varepsilon(x)=\varepsilon^{-n}\,\psi(x/\varepsilon),\qquad(\psi_\varepsilon*\varphi)(x)=\int_E\psi_\varepsilon(y)\,\varphi(x-y)\,dy.$$
--   Then $\psi_\varepsilon*\varphi\to\varphi$ in the topology of $\mathcal S(E)$ as $\varepsilon\to0^+$: for all $k,m\in\mathbb N$,
--   $$\sup_{x\in E}\,\|x\|^k\,\big\|D^m(\psi_\varepsilon*\varphi-\varphi)(x)\big\|\longrightarrow0.$$
--   This covers in particular mollifiers $\psi\in C_c^\infty$, and band-limited kernels (Fourier transform compactly supported), which are Schwartz but not compactly supported.
--
--   In the source, the approximation of the identity in Lemma 9.3.2.1 (proof, pp. 423–424) uses exactly such kernels: $\beta_m(t)=m\,\alpha_0(t^m)$ (9.3.2.3) on $\mathbb R_{>0}$, where $\alpha_0$ is the inverse Fourier transform of a cut-off $\phi_0$ with $\phi_0(0)=1$; in the coordinate $x=\log t$ this is $\beta_m(e^x)=m\,\psi(mx)$ with $\psi(x)=\alpha_0(e^x)$ Schwartz and $\int\psi=1$, i.e. the family $\psi_\varepsilon$ with $\varepsilon=1/m$.
--
--   **Formalization Note.** $\mathcal S(E)$ with its Fréchet topology is Mathlib's `𝓢(E, ℂ)`; the convolution is `SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)`, which Mathlib defines through the Fourier transform and which agrees pointwise with the integral convolution `ψ ⋆ φ` (`SchwartzMap.convolution_apply`). The dilated kernels are given as a family `ψε` of Schwartz maps with $\psi_\varepsilon(x)=\varepsilon^{-n}\psi(\varepsilon^{-1}x)$ for $\varepsilon>0$ (such a family exists: compose with the linear isomorphism $x\mapsto\varepsilon^{-1}x$); its values for $\varepsilon\le0$ are irrelevant because the limit is taken along $\varepsilon\to0^+$. The measure is the Lebesgue measure `volume` of the inner product space.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 423–424, proof of Lemma 9.3.2.1 (dilated band-limited kernels $\beta_m(t)=m\alpha_0(t^m)$, (9.3.2.3), approximating the identity)

import Mathlib

open MeasureTheory Filter Topology
open scoped SchwartzMap

set_option autoImplicit false

namespace ApproxIdentity

theorem tendsto_schwartz_convolution_dilate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ψ φ : 𝓢(E, ℂ)) (hψ : ∫ x : E, ψ x = 1) (ψε : ℝ → 𝓢(E, ℂ))
    (hψε : ∀ ε : ℝ, 0 < ε → ∀ x : E, ψε ε x = ((ε ^ Module.finrank ℝ E)⁻¹ : ℂ) * ψ (ε⁻¹ • x)) :
    Tendsto (fun ε : ℝ => SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (ψε ε) φ)
      (𝓝[>] 0) (𝓝 φ) := by sorry

end ApproxIdentity
