-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
-- name    : AutomorphicForm.exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1cc60bda-3bd2-5b1c-b8de-f88ec11e9b50
-- title:
--   Coarse geometric expansion of the truncated twisted GL₂ kernel
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, let $0<\alpha<\beta$ be reals, and let $\Phi_L\subseteq \mathrm{GL}_2(\mathbb A_L)$ be a subset of the determinant slab $S=\{g:\|\det g\|_L\in[\alpha,\beta]\}$, where $\|\cdot\|_L$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the modulus of the distributive Haar character, and let $\Phi_L$ be a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to the Haar measure `adelicGLHaar` restricted to $S$. Fix a Haar measure $\nu_{Z}$ on $\mathbb A_L^\times$ (with its Borel structure) and a fundamental domain $\Omega_L$ for the image of $L^\times$. Let $D$ be an idelic Galois descent datum, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the continuous ring automorphisms of $\mathbb A_L$ extending the action on $L$, let $\sigma$ be an automorphism such that every element of $\mathrm{Gal}(L/K)$ is an integer power of $\sigma$, and write $\sigma_{\mathbb A}$ for the induced map `sigmaAdelicAct` on $\mathrm{GL}_2(\mathbb A_L)$. Let $\xi_L$ be a homomorphism from the full unit group $\mathbb A_L^\times$ (as the top subgroup) to $\mathbb C^\times$, continuous as a $\mathbb C$-valued function and trivial on the image of $L^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb A_L)\to\mathbb C$ be continuous with compact support and factorisable, i.e. $\varphi(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ compactly supported and given by a smooth function of the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant with compact support. For $x,y$ put $K^\sigma_\varphi(x,y)=\sum_{\gamma\in\mathrm{GL}_2(L)}\varphi(x^{-1}\gamma\,\sigma_{\mathbb A}(y))$, let $\mathrm{ct}$ denote the constant term $f\mapsto\big(g\mapsto\int f(u(t)g)\,d\nu(t)\big)$ along $t\mapsto u(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, where $\nu$ is the `ν` field of `productionPinsOf L ΦL _ _ (adelicBox L)`, namely the additive adelic Haar measure conditioned on the adelic box, and let $\Lambda^{T}f=f-\mathbf 1_{\{H>T\}}\cdot\mathrm{ct}(f)$ for $H$ the adelic height. Then there is $R_0\in\mathbb R$ such that for every $R\ge R_0$, writing $\Phi_0$ for `canonicalTruncationDomain L α β` and $z\cdot x$ for the product of the central scalar matrix of $z$ with $x$,
--   $$\int_{\Phi_0}\!\int_{\Omega_L}\xi_L(z)\,\Lambda^{e^R}\!\big[y\mapsto K^\sigma_\varphi(x,y)\big](z\cdot x)\,d\nu_Z\,dg-\int_{\Phi_L}\!\int_{\Omega_L}\xi_L(z)\!\!\sum_{\delta\in\mathcal C_{\mathrm{ce}}}\!\!\varphi\big(x^{-1}\delta\,\sigma_{\mathbb A}(z\cdot x)\big)d\nu_Z\,dg$$
--   equals
--   $$\int_{\Phi_0}\!\int_{\Omega_L}\xi_L(z)\Big[\sum_{\delta\in\mathcal C_{\mathrm{par}}}\varphi\big(x^{-1}\delta\,\sigma_{\mathbb A}(z\cdot x)\big)-\mathbf 1_{\{H>e^R\}}(z\cdot x)\,\mathrm{ct}\big[y\mapsto K^\sigma_\varphi(x,y)\big](z\cdot x)\Big]d\nu_Z\,dg,$$
--   where $\mathcal C_{\mathrm{ce}}$ is the set of $\delta\in\mathrm{GL}_2(L)$ whose $\sigma$-conjugacy class has norm class (via `normClassMap`) equal to the $\mathrm{GL}_2(K)$-conjugacy class of some $\gamma$ whose characteristic polynomial has no root in $K$ or which is a scalar matrix, and $\mathcal C_{\mathrm{par}}$ is the analogous set for $\gamma$ with two distinct eigenvalues in $K$, or with a repeated eigenvalue and non-scalar; all inner sums are unordered sums over these sets.
--
--   This is the coarse geometric expansion of the $\sigma$-twisted $\mathrm{GL}_2$ kernel integral in the shape used for the twisted (base change) trace formula: after truncation at height $e^R$ the central and elliptic norm cells, being invariant and hence integrable over any fundamental domain for the determinant slab, may be read off on $\Phi_L$, while the hyperbolic and unipotent cells together with the truncation correction remain on the canonical truncation domain. It is used in the analysis of the twisted geometric remainder, feeding the comparison of twisted orbital sums with the base-change identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem
    AutomorphicForm.exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφf : IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
              (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
