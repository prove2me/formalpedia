-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
-- name    : AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/4eb65187-8be2-5f04-b118-3654fcfa9516
-- title:
--   Affine truncated slab integral over the twisted diagonal centraliser
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals, let $D$ be an idèle Galois descent datum for $\mathcal O_L$ over $K$ (a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{RingAut}(\mathbb A_L)$ whose values are continuous and compatible with $L\to\mathbb A_L$), and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the group of integer powers of $\sigma$. Let $H\le\mathrm{GL}_2(\mathbb A_L)$ be a closed subgroup consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which $\sigma_D(h)h^{-1}$ is central, $\sigma_D$ being the entrywise action of $D(\sigma)$; let $\mu_H$ be a Haar measure on $H$ that is also right invariant. Let $\Lambda_0\le\mathrm{GL}_2(L)$ consist exactly of the $\gamma$ with vanishing $(1,0)$ and $(0,1)$ entries and $\gamma_{00}/\gamma_{11}$ in the image of $K\to L$. Then there exist $\kappa_0>0$ and a set $\Omega\subseteq H$ which is a fundamental domain, for $\mu_H$, of the subgroup of $H$ induced by the image of $\Lambda_0$ under the entrywise map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb A_L)$, with the following property. Write $S=\{g:\|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is the idèle norm given by the Haar modulus on $\mathbb A_L$; write $\mathrm H$ for the adelic height (the product of the archimedean and finite heights of the components of an element of $\mathrm{GL}_2(\mathbb A_L)$), and $w$ for the image of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb A_L)$. For all $y\in\mathrm{GL}_2(\mathbb A_L)$ and $R\in\mathbb R$, with $F(h)=\mathbf 1_S(hy)\bigl(1-\mathbf 1[e^R<\mathrm H(hy)]-\mathbf 1[e^R<\mathrm H(w\,hy)]\bigr)$ a complex-valued function of $h\in H$: first, the lower integral of $\|F\|$ over $\Omega$ equals $\kappa_0\,\bigl|2R-\log\mathrm H(y)-\log\mathrm H(wy)\bigr|$ in $[0,\infty]$; secondly, if $\mathrm H(y)\,\mathrm H(wy)\le e^{2R}$, then $F$ is integrable on $\Omega$ for $\mu_H$ and $\int_\Omega F\,d\mu_H=\kappa_0\bigl(2R-\log\mathrm H(y)-\log\mathrm H(wy)\bigr)$, viewed in $\mathbb C$.
--
--   This is the exact volume computation for the twisted diagonal centraliser in the adelic winding/truncation argument: the determinant slab cuts the central idèle norm to a shell of fixed logarithmic width, while the truncation bracket is $\pm$ the indicator of a norm shell of logarithmic length $|2R-\log\mathrm H(y)\mathrm H(wy)|$, so that the truncated integral is affine in $R$ with a slope $\kappa_0$ depending only on the Haar normalisation, on $\alpha,\beta$ and on $[L:K]$. It is used by the results that extract a winding datum and compare the hyperbolic term with sums of Hecke coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ Ω : Set H,
      IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH ∧
      ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
        (∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))‖ₑ ∂μH =
          ENNReal.ofReal (κ₀ * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))|)) ∧
        (NumberField.AdelicHeight.adelicHeight L y *
            NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) ≤ Real.exp (2 * R) →
          IntegrableOn (fun h : H => Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))) Ω μH ∧
          ∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)) ∂μH =
            ((κ₀ * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
              - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) : ℝ) : ℂ)) := by sorry
