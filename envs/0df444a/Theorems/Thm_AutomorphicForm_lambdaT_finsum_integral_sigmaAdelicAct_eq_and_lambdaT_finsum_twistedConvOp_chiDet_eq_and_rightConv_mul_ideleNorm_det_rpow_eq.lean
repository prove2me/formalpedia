-- Prove2me | Theorems.Thm_AutomorphicForm_lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq
-- name    : AutomorphicForm.lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/ede3e1b3-5be2-5195-bd24-668ad4819679
-- title:
--   Twisted truncated kernel versus untwisted ξ₀-kernel
-- statement:
--   Let $K \subseteq L$ be number fields, $0 < \alpha < \beta$ reals, $\Phi_L$ a set in $\mathrm{GL}_2(\mathbb{A}_L)$, $\nu_{Z_L}$ a Haar measure on the ideles $\mathbb{A}_L^\times$ (with a Borel measurable structure on that group) and $\Omega_L$ a set of ideles. Let $D$ consist of a homomorphism from $\mathrm{Aut}_K(L)$ to continuous ring automorphisms of $\mathbb{A}_L$ compatible with $L \to \mathbb{A}_L$, let $\sigma : L \simeq_K L$, and write $\sigma_{\mathbb{A}}$ for the induced map on $\mathrm{GL}_2(\mathbb{A}_L)$ and on ideles. Let $\xi_L : \mathbb{A}_L^\times \to \mathbb{C}^\times$ be trivial on the principal ideles and satisfy $|\xi_L(z)| = \|z\|^w$ for the idele norm $\|\cdot\|$ (the module of the distributive Haar character) and a real $w$; let $\Phi_0$ lie in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$ and be a fundamental domain for the image of $\mathrm{GL}_2(L)$ in the adelic Haar measure restricted to that slab. Let $\xi'(z) = \xi_L(\sigma z)$, let $\xi_0$ satisfy $\xi_0(z)\|z\|^w = \xi'(z)$, and let $\varphi'(g) = \varphi(g)\|\det g\|^{w/2}$ for a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$. Throughout, truncation is the operator $\lambda^T$ sending $f$ to $f - \mathbf{1}_{\{\text{adelic height} > T\}} \cdot (\text{constant term of } f)$, where the constant term integrates $t \mapsto f(u(t)g)$ over upper unipotent matrices against the adelic additive Haar measure conditioned on the adelic box, and $T = e^R$; the auxiliary data $\Phi_L$, the levels $\mathrm{levelOne} \sqcap \ker(\text{archimedean part})$ and the Hecke generators enter only through this package. Then for every real $R$ and every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ three assertions hold. First, $\lambda^{e^R}$ applied to $y \mapsto \sum_{\delta \in \mathrm{GL}_2(L)/Z} \int \xi_L(z)\,\varphi(x^{-1}\delta\, \sigma_{\mathbb{A}}^{-1}(z y))\,d\nu_{Z_L}(z)$ and evaluated at $x$ equals $\lambda^{e^R}$ applied to $y \mapsto \sum_{\delta} \int \xi_0(z)\,\varphi'(x^{-1}\delta z y)\,d\nu_{Z_L}(z)$ and evaluated at $\sigma_{\mathbb{A}}^{-1}(x)$, the sums being finite sums over the quotient of $\mathrm{GL}_2(L)$ by its centre with chosen representatives and $z$ acting by the central scalar matrix. Secondly, with $b = \nu_{Z_L}(\Omega_L \cap \{z : \|\det(zI)\| \in [\alpha,\beta]\})$, $\lambda^{e^R}$ applied to $y \mapsto (b/\mathrm{vol}(\Phi_0)) \sum_{\chi} (\text{rightConv}(\chi \circ \det \circ\, \sigma_{\mathbb{A}}, \varphi))(x)\, \chi^{-1}(\det y)$, summed over the continuous characters $\chi$ of $\mathbb{A}_L^\times$ that are trivial on principal ideles and satisfy $\chi^2 = \xi_L$, and evaluated at $x$, equals $\lambda^{e^R}$ applied to $y \mapsto (b/\mathrm{vol}(\Phi_c)) \sum_{\chi} \left(\int \varphi'\,(\chi \circ \det)\right) \chi(\det x)\chi^{-1}(\det y)$ over the analogous set of $\chi$ with $\chi^2 = \xi_0$, and evaluated at $\sigma_{\mathbb{A}}^{-1}(x)$, where $\Phi_c$ is the canonical truncation domain of the slab $[\alpha,\beta]$ and all volumes are for adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$. Thirdly, for every $\psi$ and every $k$ in the adelic maximal compact subgroup (finite part integral, archimedean components row isometries), $\int \psi(kg)\|\det(kg)\|^{w/2}\varphi(g)\,dg = \int \psi(kg)\varphi'(g)\,dg$.
--
--   This is the dictionary translating the blocks of the $\sigma$-twisted truncated kernel, formed with the character $\xi_L$ and the test function $\varphi$, into the untwisted blocks for the character $\xi_0 = (\xi_L \circ \sigma)\|\cdot\|^{-w}$ and the rescaled test function $\varphi'$, read along the twisted diagonal $x \mapsto \sigma_{\mathbb{A}}^{-1}(x)$; the third clause records the compatibility of the rescaling with right convolution at points of the maximal compact subgroup. It feeds the comparison of truncated inner products of twisted kernels in the base-change style trace identity for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq.lean

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
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.lambdaT_finsum_integral_sigmaAdelicAct_eq_and_lambdaT_finsum_twistedConvOp_chiDet_eq_and_rightConv_mul_ideleNorm_det_rpow_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ))
    (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ = ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩)
    (ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (φ φ' : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) :
    ∀ (R : ℝ) (x : AdelicGL2 (𝓞 L) L),
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) =
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ' (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) ∧
      ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x) =
      (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) (AutomorphicForm.canonicalTruncationDomain L α β)).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξ₀ χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      (∫ g, φ' g * chiDet (𝓞 L) L χ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) *
                        (chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) ∧
      (∀ (ψ : AdelicGL2 (𝓞 L) L → ℂ) (k : adelicMaximalCompact L),
        rightConv L (fun g : AdelicGL2 (𝓞 L) L => ψ g *
            (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ
          (k : AdelicGL2 (𝓞 L) L) =
        rightConv L ψ φ' (k : AdelicGL2 (𝓞 L) L)) := by sorry
