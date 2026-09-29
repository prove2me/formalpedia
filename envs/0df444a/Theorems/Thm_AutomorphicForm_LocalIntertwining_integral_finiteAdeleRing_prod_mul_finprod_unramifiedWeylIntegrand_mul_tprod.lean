-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
-- name    : AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9f7ed403-c668-5772-b0c2-b552c4e39c63
-- title:
--   Finite-adelic unramified intertwining integral as an Euler product
-- statement:
--   Let $F$ be a number field, with the finite adele ring $\mathbb{A}_f =$ `FiniteAdeleRing (𝓞 F) F` carrying a measurable structure that is the Borel structure of its topology, and let $\nu$ be an additive Haar measure on it. Let $S$ be a finite set of nonzero primes of $\mathcal{O}_F$; each completion $F_v$ likewise carries its Borel structure, and for each $v$ an additive Haar measure $\mu_v$ on $F_v$, an arbitrary function $h_v : F_v \to \mathbb{C}$, a unit $\varpi_v \in F_v^{\times}$ and a homomorphism $\chi_v : F_v^{\times} \to \mathbb{C}^{\times}$ are given. Assume that for $v \notin S$: the valuation of $\varpi_v$ is $\mathrm{ofAdd}(-1)$, $\chi_v$ is trivial on units of valuation $1$, and $\lVert \chi_v(\varpi_v)\rVert \le 1$. Let $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$. Write $\widehat{\mathcal{O}} = \{x : x_v \in \mathcal{O}_v \text{ for all } v\}$ (the set `integralFiniteAdeles`), and for $v \notin S$ let $\varphi_v^{\circ}(y)$ be the sum of the indicator of $\mathcal{O}_v$ with value $1$ and the indicator of its complement with value $\mathrm{charExt}(\chi_v^{-1})(y)\,\mathrm{modulus}(y)^{-(2s+1)}$, where $\mathrm{charExt}(\chi_v^{-1})(y)$ is $\chi_v(y)^{-1}$ for $y \ne 0$ and $0$ at $y=0$, and $\mathrm{modulus}(y)$ is the scaling factor of additive Haar measure under multiplication by $y$ (and $0$ at $y=0$). Then
--   $$\nu(\widehat{\mathcal{O}})^{-1}\Bigl(\int_{\mathbb{A}_f} \prod_{v \in S} h_v(x_v) \cdot \prod^{\mathrm{f}}_{v \notin S} \varphi_v^{\circ}(x_v)\, d\nu\Bigr) \prod_{v \notin S}\bigl(1 - \chi_v(\varpi_v) N(v)^{-2s}\bigr) = \prod_{v \in S} \Bigl(\mu_v(\mathcal{O}_v)^{-1}\int_{F_v} h_v\, d\mu_v\Bigr) \prod_{v \notin S}\bigl(1 - \chi_v(\varpi_v) N(v)^{-(2s+1)}\bigr),$$
--   where $N(v) =$ `Ideal.absNorm v.asIdeal`, the measures of $\widehat{\mathcal{O}}$ and of $\mathcal{O}_v$ are taken as real numbers and coerced to $\mathbb{C}$, the product over $v \notin S$ inside the integral is a `finprod`, and the two products over $v \notin S$ of Euler factors are infinite products (`tprod`).
--
--   This is the finite-adelic assembly of the rank-one Gindikin–Karpelevich computation: off a finite set $S$ the unramified local intertwining integrands contribute the Euler factor ratio $\prod_{v \notin S}(1 - \chi_v(\varpi_v)N(v)^{-(2s+1)})/(1 - \chi_v(\varpi_v)N(v)^{-2s})$, while at the places of $S$ arbitrary local functions are kept as normalised local integrals. It combines the local evaluation `integral_unramifiedWeylIntegrand_adicCompletion` with the convergence estimate `tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top`, and is used by the corresponding statement over the full adele ring for pure tensors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    (ν.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * (∫ x, (∏ v ∈ S, h v (x v))
              * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                      (fun _ => (1 : ℂ)) (x v.1)
                    + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                        (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x v.1))) ∂ν)
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
            * ∫ y, h v y ∂(μ v)))
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) := by sorry
