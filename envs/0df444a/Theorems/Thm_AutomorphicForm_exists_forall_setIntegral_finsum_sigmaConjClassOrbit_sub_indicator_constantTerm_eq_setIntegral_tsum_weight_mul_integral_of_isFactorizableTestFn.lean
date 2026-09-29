-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn
-- name    : AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e09604e3-d224-5950-a813-9071d73b8554
-- title:
--   One twisted hyperbolic class: truncated term equals weighted orbital integrals
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$, let $\nu_{Z}$ be a Haar measure on $\mathbb{A}_L^\times$ and $\Omega_L$ a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to it. Let $D$ be an idelic Galois descent datum (a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, compatible with $L\to\mathbb{A}_L$ and continuous), let $\sigma$ be a $K$-automorphism of $L$ with every $\tau\in\mathrm{Gal}(L/K)$ in $\langle\sigma\rangle$, and write $\sigma_{\mathbb{A}}$ for the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$, $c(z)$ for the central scalar matrix attached to $z\in\mathbb{A}_L^\times$. Let $\xi_L$ be a homomorphism from $\mathbb{A}_L^\times$ (as the top subgroup) to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function and trivial on principal ideles. Let $c>0$ and $u,d_1,d_2$ be real, $T_c$ compact, $\Phi_L$ a set of adelic matrices, and $\Phi_0$ a fundamental domain for the image of $\mathrm{GL}_2(L)$ with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to the slab $\{g:\ \|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]\}$, with $\Phi_0$ contained in that slab and in $\bigcup_{y\in T_c}(\cdot\, y)$-translates of the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (integral finite part, archimedean local heights $\ge c$, $x$-windows $\le u^2$, archimedean determinant norms in $[d_1,d_2]$). Let $\delta_0\in\mathrm{GL}_2(L)$ be diagonal (entries $(1,0)$ and $(0,1)$ vanishing) with $N_{L/K}((\delta_0)_{00}/(\delta_0)_{11})\neq 1$; let $I$ be the set of $\delta$ such that $\delta_0^{-1}g^{-1}\delta\,\sigma(g)$ is central for some $g\in\mathrm{GL}_2(L)$, let $\Lambda$ be the subgroup of $\gamma$ with $\delta_0^{-1}\gamma\delta_0\sigma(\gamma)^{-1}$ central, and let $r:\iota\to\mathrm{GL}_2(L)$, with $\iota$ countable, pick out left $\Lambda$-coset representatives, in the sense that each $\gamma$ satisfies $(r\,i)^{-1}\gamma\in\Lambda$ for exactly one $i$. Finally let $\varphi$ be factorizable: $\varphi(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ given by a smooth function of the archimedean matrix entries and compactly supported, and $f_{\mathrm{fin}}$ locally constant and compactly supported. Then there is $R_0$ such that for every $R\ge R_0$: the function $$x\mapsto \int_{\Omega_L}\xi_L(z)\Big(\sum_{\delta\in I}^{\mathrm{f}}\varphi\big(x^{-1}\delta\,\sigma_{\mathbb{A}}(c(z)x)\big)-\mathbf 1[\mathrm H(c(z)x)>e^R]\int\textstyle\sum^{\mathrm{f}}_{\delta\in I,\ \delta_{10}=0}\varphi\big(x^{-1}\delta\,\sigma_{\mathbb{A}}(n(t)c(z)x)\big)\,d t\Big)\,d\nu_Z(z)$$ is integrable on $\Phi_0$, where $\mathrm H$ is the adelic height, $n(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, the sums are finsums over the indicated subsets, and $dt$ is the adelic additive Haar measure conditioned on the adelic box (the level and Hecke data $\Phi_L$, $\mathrm{levelOne}\sqcap$ the finite-adelic subgroup and $\mathrm{heckeGen}$ enter only as inert packaging); the function $$x\mapsto\sum_{i}\Big(1-\mathbf 1[\mathrm H(y_i)>e^R]-\mathbf 1[\mathrm H(w\,y_i)>e^R]\Big)\int\xi_L(z)\varphi\big(y_i^{-1}\delta_0\,\sigma_{\mathbb{A}}(c(z)y_i)\big)\,d\nu_Z(z),\qquad y_i=(r\,i)^{-1}x,$$ with $w$ the adelic Weyl element and the $z$-integral over all of $\mathbb{A}_L^\times$, is integrable on $\Phi_0$; and the two integrals over $\Phi_0$ against the adelic Haar measure are equal.
--
--   This is the treatment of a single regular twisted (hyperbolic) class on the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$: after truncation at height $e^R$, the contribution of the class, with the constant term along the unipotent radical subtracted, is rewritten as a sum over $\Lambda$-cosets of twisted orbital integrals at $\delta_0$ weighted pointwise by $1-\mathbf 1[\mathrm H>e^R]-\mathbf 1[\mathrm H\circ w>e^R]$. It feeds the two later statements that assemble the full hyperbolic contribution, one combining the regular classes with the remaining orbital terms and one recording the torus-shell form of that combination.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)

    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x in Φ₀, ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
