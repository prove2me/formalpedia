-- Prove2me | Theorems.Thm_AutomorphicForm_resKernel_twist_and_lambdaT_resKernel_diag
-- name    : AutomorphicForm.resKernel_twist_and_lambdaT_resKernel_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/1374ae6f-e266-50e3-9eb9-e8b220897edc
-- title:
--   Twist transport and truncated diagonal of the residual kernel
-- statement:
--   Let $K$ be a number field with adele ring $\mathbb{A}$, let $0<\alpha<\beta$ be reals, let $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A})$, let $\nu_{Z,K}$ be a measure on $\mathbb{A}^\times$ and $\Omega_K\subseteq\mathbb{A}^\times$, let $\xi_K,\xi_{0,K}\colon \mathbb{A}^\times\to\mathbb{C}^\times$ be characters (homomorphisms from the full subgroup $\top$), let $w\in\mathbb{R}$, and let $f\colon \mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ be continuous with compact support. Write $\alpha_m\colon\mathbb{A}^\times\to\mathbb{R}^\times$ for the homomorphism induced by the distributive Haar character of $\mathbb{A}$, assume $\alpha_m$ takes positive values, and assume $\xi_{0,K}(z)=\xi_K(z)\,\alpha_m(z)^{-w}$ for all $z$, the power being formed by `cpowChar`. For a character $\xi$ let $S(\xi)$ be the set of homomorphisms $\chi\colon\mathbb{A}^\times\to\mathbb{C}^\times$ with $\chi(z)^2=\xi(z)$ for all $z$, with $\chi$ trivial on the image of $K^\times$, and with $z\mapsto\chi(z)$ continuous; put $\chi\circ\det$ for `chiDet`, $\|\cdot\|$ for the idele norm $z\mapsto\mathrm{distribHaarChar}(z)$, and let $\mu$ be the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A})$. Three assertions are made. First, for all $x,y$, $$\sum^{\mathrm{f}}_{\chi\in S(\xi_K)}\Big(\int f\,\chi(\det g)\,d\mu\Big)\chi(\det x)\chi^{-1}(\det y)=\|\det x\|^{w/2}\big(\|\det y\|^{w/2}\big)^{-1}\sum^{\mathrm{f}}_{\chi\in S(\xi_{0,K})}\Big(\int f(g)\|\det g\|^{w/2}\chi(\det g)\,d\mu\Big)\chi(\det x)\chi^{-1}(\det y),$$ the sums being finsums. Second, with $c_0=\nu_{Z,K}\big(\Omega_K\cap\{z:\|\det(\mathrm{diag}(z,z))\|\in[\alpha,\beta]\}\big)/\mu(\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta)$ (real parts, coerced to $\mathbb{C}$), and with `lambdaT` taken for the conditional measure of the adelic additive Haar measure on `adelicBox K` supplied by `productionPinsOf` (level subgroups $M\mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup`, generators `heckeGen`), the unipotents $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, the height `adelicHeight K` and threshold $e^R$: for all $R$ and $x$, applying `lambdaT` to $y'\mapsto c_0\sum^{\mathrm{f}}_{\chi\in S(\xi_K)}(\int f\,\chi\circ\det)\chi(\det x)\chi^{-1}(\det y')$ and evaluating at $x$ gives $\mathbf 1_{\{\mathrm{adelicHeight}_K(x)\le e^R\}}\cdot c_0\sum^{\mathrm{f}}_{\chi\in S(\xi_K)}\int f\,\chi\circ\det$. Third, for each $R$ this diagonal function of $x$ is integrable on `canonicalTruncationDomain K α β` for $\mu$.
--
--   The statement isolates the residual (Eisenstein) block of the $\mathrm{GL}_2$ adelic kernel attached to a central character: it records how that block transforms when the test function is twisted by $\|\det\|^{w/2}$ and the central character correspondingly shifted, and it evaluates the one-cusp truncation operator on its diagonal, where the block is left invariant by unipotent translation because $\det$ is trivial there. Both halves feed the later analysis of set integrals of truncated kernels over the canonical truncation domain, where the residual contribution must be separated from the cuspidal one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_resKernel_twist_and_lambdaT_resKernel_diag.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.resKernel_twist_and_lambdaT_resKernel_diag
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : MeasureTheory.Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (_hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ξ₀K ⟨z, Subgroup.mem_top z⟩ = ξK ⟨z, Subgroup.mem_top z⟩ * cpowChar αm hαm (((-w : ℝ) : ℂ)) z),
    (∀ x y : AdelicGL2 (𝓞 K) K,
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y)) =
      ((((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (w / 2) : ℝ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) : ℝ) : ℂ)⁻¹) *
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξ₀K χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, (f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y))) ∧
    (∀ (R : ℝ) (x : AdelicGL2 (𝓞 K) K),
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x) =
      (if NumberField.AdelicHeight.adelicHeight K x ≤ Real.exp R then 1 else 0) * (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
        ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
          (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    (∀ R : ℝ, IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
      (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)) (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
