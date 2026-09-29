-- Prove2me | Theorems.Thm_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod
-- name    : AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/8e8c80a8-8200-5ee7-a800-2de07551944c
-- title:
--   Transport of torus-shell integrals to Ω_L×Ω_K
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ Galois, let $\alpha,\beta\in\mathbb R$, let $\nu_{Z_L}$ be a Haar measure on $\mathbb A_L^\times$ with Borel structure, and let $\Omega_L$ be a fundamental domain for the group of principal ideles (the range of $L^\times\to\mathbb A_L^\times$) acting on $\mathbb A_L^\times$ with respect to $\nu_{Z_L}$. Let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism $\tau\mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb A_L$ that are continuous and compatible with $L\to\mathbb A_L$, and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$. Let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb A_L)$ consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which $\sigma_D(h)h^{-1}$ is central, where $\sigma_D$ is $\mathrm{GL}_2$ applied entrywise to $D.\mathrm{act}\,\sigma$; let $\mu_H$ be a left and right invariant Haar measure on $H$. Let $\Lambda_0\le\mathrm{GL}_2(L)$ consist exactly of the $\gamma$ with vanishing $(1,0)$ and $(0,1)$ entries and $\gamma_{00}/\gamma_{11}\in\mathrm{image}(K\to L)$. Let $\nu_K$ be a Haar measure on $\mathbb A_K^\times$ with fundamental domain $\Omega_K$ for the principal ideles of $K$, and let $\theta:\mathbb A_K^\times\to\mathbb A_L^\times$ be a continuous injective homomorphism carrying the principal idele of $k\in K^\times$ to that of its image in $L$. Assume finally $c_H>0$ is such that for every measurable $f:\mathrm{GL}_2(\mathbb A_L)\to[0,\infty]$ one has $\int_H f\,d\mu_H=c_H\int\!\!\int f\bigl(z\cdot I\cdot\mathrm{diag}(\theta a,1)\bigr)\,d\nu_K(a)\,d\nu_{Z_L}(z)$, where $z\cdot I$ denotes the central scalar matrix. Then, writing $\Psi(z,a)=z\cdot I\cdot\mathrm{diag}(\theta a,1)$ and $\Lambda$ for the subgroup of $H$ induced by the image of $\Lambda_0$ in $\mathrm{GL}_2(\mathbb A_L)$ under entrywise $L\to\mathbb A_L$: (i) $\{h\in H:\ h=\Psi(z,a)\text{ for some }z\in\Omega_L,\ a\in\Omega_K\}$ is a fundamental domain for $\Lambda$ in $H$ with respect to $\mu_H$; and (ii) for every fundamental domain $\Omega\subseteq H$ for $\Lambda$ with respect to $\mu_H$, every $y\in\mathrm{GL}_2(\mathbb A_L)$ and every $R\in\mathbb R$, the complex-valued integrand $T(g)=\mathbf 1_{\{\|\det\|\in[\alpha,\beta]\}}(gy)\cdot\bigl(1-\mathbf 1_{\{e^R<\mathrm{ht}\}}(gy)-\mathbf 1_{\{e^R<\mathrm{ht}(w\,\cdot\,)\}}(gy)\bigr)$ — with $\|\det\|$ the idele norm of the determinant (the distributive Haar character), $\mathrm{ht}$ the adelic height of $L$, and $w$ the image in $\mathrm{GL}_2(\mathbb A_L)$ of the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ — satisfies $\int^-_\Omega\|T(h)\|_e\,d\mu_H=c_H\int^-_{\Omega_L\times\Omega_K}\|T(\Psi(p))\|_e\,d(\nu_{Z_L}\otimes\nu_K)$, $T$ is integrable on $\Omega$ for $\mu_H$ if and only if $T\circ\Psi$ is integrable on $\Omega_L\times\Omega_K$ for $\nu_{Z_L}\otimes\nu_K$, and $\int_\Omega T\,d\mu_H=c_H\int_{\Omega_L\times\Omega_K}T\circ\Psi\,d(\nu_{Z_L}\otimes\nu_K)$.
--
--   This is the fundamental-domain transport step for the twisted centraliser $H$ of $\mathrm{GL}_2$ over the adeles of $L$: the test-function identity for $\mu_H$ is upgraded to an identification of an explicit product set as a fundamental domain for the rational points $\Lambda_0$, and integrals of the windowed torus-shell integrand over an arbitrary fundamental domain are rewritten as integrals over $\Omega_L\times\Omega_K$. It is used by [`AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq`](thm.html#AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq), which combines it with the evaluation of the resulting product integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod.lean

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

theorem AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_torusShell_eq_mul_setLIntegral_prod
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL) :
    IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H)
      {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
        (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} μH ∧
    ∀ (Ω : Set H), IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH →
      ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
        (∫⁻ h in Ω, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)))‖ₑ ∂μH =
          ENNReal.ofReal cH * ∫⁻ p in ΩL ×ˢ ΩK, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))‖ₑ ∂(νZL.prod νK)) ∧
        (IntegrableOn (fun h : H => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)))) Ω μH ↔
          IntegrableOn (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))) (ΩL ×ˢ ΩK) (νZL.prod νK)) ∧
        ∫ h in Ω, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))) ∂μH =
          (cH : ℂ) * ∫ p in ΩL ×ˢ ΩK, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) ∂(νZL.prod νK) := by sorry
