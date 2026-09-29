-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
-- name    : AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/d36c84e8-c95f-5407-96ba-5ad98d5be677
-- title:
--   Adelic factorisation of an unramified intertwining integral
-- statement:
--   Let $F$ be a number field, let the adele ring $\mathbb{A}_F$ carry a Borel measurable structure and an additive Haar measure $\mu$, let $S$ be a finite set of maximal ideals of $\mathcal{O}_F$, and for each maximal ideal $v$ let the completion $F_v$ carry a Borel structure and an additive Haar measure $\mu_v$. Let $f$ be a complex-valued function on the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$, let $h_v\colon F_v\to\mathbb{C}$ be arbitrary functions, let $\varpi_v\in F_v^\times$ satisfy $\mathrm{v}(\varpi_v)=\mathrm{ofAdd}(-1)$ for all $v\notin S$, and let $\chi_v\colon F_v^\times\to\mathbb{C}^\times$ be homomorphisms such that for $v\notin S$ one has $\chi_v(u)=1$ whenever $\mathrm{v}(u)=1$ and $\lVert\chi_v(\varpi_v)\rVert\le 1$. Let $s\in\mathbb{C}$ with $\operatorname{Re}s>1/2$. Then the product of: the inverse of $\mu$ of the adelic box (those adeles whose infinite part lies, through the canonical isomorphism with the mixed space, in the fundamental domain of the lattice basis of $\mathcal{O}_F$, and whose finite part has every component in $\mathcal{O}_v$); the integral over $\mathbb{A}_F$ against $\mu$ of $f$ evaluated on the infinite part, times $\prod_{v\in S}h_v(x_v)$, times the finitary product over $v\notin S$ of $\mathbf{1}_{\mathcal{O}_v}(x_v)+\mathbf{1}_{F_v\setminus\mathcal{O}_v}(x_v)\,\chi_v^{-1}(x_v)\,|x_v|^{-(2s+1)}$, where $\chi_v^{-1}(y)$ means $\chi_v(y)^{-1}$ for $y\ne 0$ and $0$ at $y=0$, and $|y|$ is the module of $y$ (the Haar scaling factor of multiplication by $y$, set to $0$ at $0$); and the infinite product $\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)N(v)^{-2s}\bigr)$, equals $2^{r_2}|d_F|^{-1/2}$ times $\int f$ times $\prod_{v\in S}\bigl(\mu_v(\mathcal{O}_v)^{-1}\int h_v\,d\mu_v\bigr)$ times $\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)N(v)^{-(2s+1)}\bigr)$, where $r_2$ is the number of complex places and $d_F$ the discriminant.
--
--   This is the global assembly, over all places at once, of the rank-one Gindikin–Karpelevich computation for $\mathrm{GL}_2$: the box-normalised adelic integral of a pure tensor whose components at $v\notin S$ are the spherical vectors splits into the archimedean integral of $f$, the normalised local integrals of $h_v$ for $v\in S$, and the ratio of unramified Euler products, here written in cross-multiplied form so that no non-vanishing assumption on the products is needed. It feeds the construction of the analytic continuation and growth estimates for normalised intertwining integrals of induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open NumberField.AdelicBox
open IsDedekindDomain
open scoped Classical in

theorem AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹
        * (∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
              * ((∏ v ∈ S, h v (x.2 v))
                * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                    (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                        (fun _ => (1 : ℂ)) (x.2 v.1)
                      + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                          (x.2 v.1)))) ∂μ)
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (∫ y, f y)
        * ((∏ v ∈ S, (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
              * ∫ y, h v y ∂(μv v)))
          * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) := by sorry
