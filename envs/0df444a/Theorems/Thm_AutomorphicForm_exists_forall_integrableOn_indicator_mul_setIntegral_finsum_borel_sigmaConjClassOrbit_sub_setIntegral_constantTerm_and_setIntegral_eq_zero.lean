-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
-- name    : AutomorphicForm.exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/730aa85b-b07b-5be6-bf03-7501de1eb454
-- title:
--   Truncated defect of a hyperbolic twisted class integrates to zero
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals, and fix a set $\Phi_L$ of adelic matrices in $\mathrm{GL}_2(\mathbb{A}_L)$ (entering only through the carrier-pins record built by `productionPinsOf` from $\Phi_L$, the levels $\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen` and the adelic box, whose measure fields are used below). Let $\nu_{Z_L}$ be a Haar measure on the ideles $\mathbb{A}_L^\times$ (with its Borel structure) and $\Omega_L$ a fundamental domain for the subgroup of principal ideles, the image of $L^\times$. Let $D$ be an idele Galois descent datum for $L/K$, that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the continuous ring automorphisms of $\mathbb{A}_L$ compatible with the action on $L$; let $\sigma$ generate $\mathrm{Gal}(L/K)$ (every $\tau$ lies in the subgroup of integral powers of $\sigma$), and write $\sigma_{\mathbb{A}}$ for the induced entrywise automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$. Let $\xi_L$ be a character of the full idele group, continuous as a $\mathbb{C}$-valued function and trivial on principal ideles. Let $c,u,d_1,d_2$ be reals with $0<c$, let $T_c$ be compact, and let $\Phi_0$ be contained in $\bigcup_{y\in T_c}\mathfrak{S}y$ for the centre-cut Siegel set $\mathfrak{S}$ of parameters $c,u,d_1,d_2$ (finite part integral, all local heights $\ge c$, all window squares $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$), contained in the slab where the idele norm of the determinant lies in $[\alpha,\beta]$, and a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to adelic Haar measure restricted to that slab. Let $\delta_0\in\mathrm{GL}_2(L)$ be diagonal (entries $(1,0)$ and $(0,1)$ vanishing) with $N_{L/K}(\delta_{0,00}/\delta_{0,11})\neq 1$, and let $I$ consist of those $\delta$ for which some $g$ satisfies $\delta_0^{-1}\,(g^{-1}\delta\,\sigma(g))$ central. Let $\varphi$ be a factorizable test function on $\mathrm{GL}_2(\mathbb{A}_L)$, i.e. $\varphi(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ given by a smooth compactly supported function of the matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support. Put, for $x\in\mathrm{GL}_2(\mathbb{A}_L)$, $a(x)=\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\bigl(x^{-1}\delta\,\sigma_{\mathbb{A}}(c(z)x)\bigr)\,d\nu_{Z_L}(z)$, the sum being the unordered sum over the set of $\gamma\in\mathrm{GL}_2(L)$ with $\gamma_{10}=0$ and $\gamma\in I$, and let $\tilde a(x)$ be the same expression with the inner sum replaced by its constant term along $t\mapsto n(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, the integral over $\mathbb{A}_L$ with respect to the adelic additive Haar measure conditioned on the adelic box, evaluated at $c(z)x$. The conclusion asserts: for every $x$ the integrand of $a(x)$ is integrable on $\Omega_L$; for every $x$ the integrand of $\tilde a(x)$ is integrable on $\Omega_L$; and there is $R_1$ such that for all $R\ge R_1$ the function $x\mapsto \mathbf{1}_{\{\,\mathrm{adelicHeight}>e^{R}\}}(x)\,(a(x)-\tilde a(x))$ is integrable on $\Phi_0$ for adelic Haar measure and its integral over $\Phi_0$ vanishes.
--
--   On the geometric side of the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension, this is the vanishing of the high-height (cuspidal) defect attached to a single regular hyperbolic twisted $\sigma$-conjugacy class, folded over the centre against an idele class character: above a fixed height threshold the class kernel restricted to the upper-triangular part agrees, after integration over the fundamental domain, with its constant term along the unipotent radical. It feeds the assembly of the truncated hyperbolic contribution as a weighted orbital integral, used in [`AutomorphicForm.exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
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

    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    (∀ x : AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
        Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) -
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              @AutomorphicForm.constantTerm _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀,
        Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) -
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              @AutomorphicForm.constantTerm _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0 := by sorry
