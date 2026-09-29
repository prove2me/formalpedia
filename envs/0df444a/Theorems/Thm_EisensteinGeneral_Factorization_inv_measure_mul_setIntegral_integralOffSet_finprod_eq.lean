-- Prove2me | Theorems.Thm_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq
-- name    : EisensteinGeneral.Factorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e80c5b15-98b1-522e-9648-4e82012dcf4a
-- title:
--   Finite-level factorisation of an adelic integral into local integrals
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal O_F$; the finite adele ring $\mathbb A_{F,f}$ carries a measurable structure that is the Borel structure of its topology, and $\nu$ is an additive Haar measure on it. Let $S$ be a finite set of maximal ideals of $\mathcal O_F$ (height-one primes), and for each such $v$ let the completion $F_v$ carry its Borel structure and an additive Haar measure $\mu_v$. Let $h_v\colon F_v\to\mathbb C$ be arbitrary functions, subject only to the requirement that for every $v\notin S$ one has $h_v(y)=1$ whenever $y$ lies in the valuation ring $\mathcal O_v$. Write $X_S=\{x\in\mathbb A_{F,f}:\ x_v\in\mathcal O_v\text{ for all }v\notin S\}$, and let `integralFiniteAdeles` be the set of $x$ with $x_v\in\mathcal O_v$ for all $v$. Then, with all measures of sets taken as real numbers and coerced to $\mathbb C$, all inverses taken in $\mathbb C$, and all integrals Bochner integrals of the possibly infinite product $\prod^{\mathrm f}_v h_v(x_v)$ (the finprod, equal to the finite product over the places where the factor is not $1$), $$\nu(\widehat{\mathcal O}_F)^{-1}\int_{X_S}\prod_v h_v(x_v)\,d\nu(x)=\prod_{v\in S}\Big(\mu_v(\mathcal O_v)^{-1}\int_{F_v}h_v\,d\mu_v\Big).$$
--
--   This is the finite-place half of the factorisation of an integral over a restricted product into local integrals, as in Tate's thesis, normalised so that the ambiguity in the choice of Haar measures cancels: no compatibility between $\nu$ and the $\mu_v$ is assumed, each integral being divided by the measure of the relevant ring of integers. It is used in the adelic Fourier-analytic and zeta-integral computations of the project, in particular in the global-to-local factorisation of zeta integrals and of Fourier transforms of products of local functions times indicator functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox
  IsDedekindDomain

theorem EisensteinGeneral.Factorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1) :
    (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x in {x : FiniteAdeleRing (𝓞 F) F |
              ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F},
            ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
          * ∫ y, h v y ∂(μ v)) := by sorry
