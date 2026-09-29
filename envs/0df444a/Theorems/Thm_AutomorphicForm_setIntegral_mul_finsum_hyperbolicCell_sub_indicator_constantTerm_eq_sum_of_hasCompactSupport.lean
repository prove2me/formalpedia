-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport
-- name    : AutomorphicForm.setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/8a4235a6-c136-5c69-a1de-f71f6376ead4
-- title:
--   Truncated twisted hyperbolic term as a finite sum over Δ_φ
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$, let $\nu_{Z_L}$ be a Haar measure on the idele group $\mathbb{A}_L^\times$ (with its Borel structure) and let $\Omega_L$ be a fundamental domain for the action of the image of $L^\times$ in $\mathbb{A}_L^\times$ on $\mathbb{A}_L^\times$ with respect to $\nu_{Z_L}$. Let $D$ be an idelic Galois descent datum for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, continuous and compatible with $L\to\mathbb{A}_L$, let $\sigma\in\mathrm{Gal}(L/K)$ generate the Galois group (every $\tau$ lies in the group of integral powers of $\sigma$), let $\xi_L$ be a homomorphism from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function and trivial on principal ideles, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ be continuous with compact support. Write $\iota$ for the entrywise map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$, $c(z)$ for the scalar matrix attached to $z\in\mathbb{A}_L^\times$, $\sigma_D$ for the entrywise action of $D(\sigma)$ on $\mathrm{GL}_2(\mathbb{A}_L)$, and for $t\in\mathrm{GL}_2(L)$ put $I(t)=\{\delta:\exists g,\ t^{-1}(g^{-1}\delta\,\sigma(g))\in Z(\mathrm{GL}_2(L))\}$, where $\sigma(g)$ is the entrywise image of $g$ under $\sigma$. Let $\mathcal{H}$ be the set of $\delta\in\mathrm{GL}_2(L)$ whose $\sigma$-twisted norm class $\mathrm{normClassMap}$ of the $\sigma$-conjugacy class of $\delta$ equals the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ lying in the hyperbolic cell, that is, with characteristic polynomial $(X-a)(X-b)$ for some $a\neq b$ in $K$. Assume: every $t\in\Delta$ is diagonal (entries $(1,0)$ and $(0,1)$ vanish) with $N_{L/K}(t_{00}/t_{11})\neq 1$; the sets $I(t)$, $t\in\Delta$, are pairwise disjoint for distinct $t,t'$; and $\mathcal{H}\subseteq\bigcup_{t\in\Delta}I(t)$. Let $\Delta_\varphi$ be a finite subset of $\Delta$ such that for every $t\in\Delta\setminus\Delta_\varphi$, all $x\in\mathrm{GL}_2(\mathbb{A}_L)$ and all $z\in\mathbb{A}_L^\times$ one has $\varphi\bigl(x^{-1}\iota(t)\,\sigma_D(c(z)x)\bigr)=0$. Then for every $R\in\mathbb{R}$ and every $x\in\mathrm{GL}_2(\mathbb{A}_L)$, $$\int_{\Omega_L}\xi_L(z)\Bigl[\sum_{\delta\in\mathcal H}\varphi\bigl(x^{-1}\iota(\delta)\sigma_D(c(z)x)\bigr)-\mathbf 1_{\{g:\,e^R<\mathrm{H}(g)\}}(c(z)x)\cdot \mathrm{CT}\,f_{\mathcal B}(c(z)x)\Bigr]\,d\nu_{Z_L}(z)=\sum_{t\in\Delta_\varphi}\int_{\Omega_L}\xi_L(z)\Bigl[\sum_{\delta\in I(t)}\varphi\bigl(x^{-1}\iota(\delta)\sigma_D(c(z)x)\bigr)-\mathbf 1_{\{g:\,e^R<\mathrm{H}(g)\}}(c(z)x)\cdot \mathrm{CT}\,f_{t}(c(z)x)\Bigr]\,d\nu_{Z_L}(z),$$ where the inner sums are finsums over the indicated sets, $\mathrm{H}$ is the adelic height of $L$, and for a function $f$ on $\mathrm{GL}_2(\mathbb{A}_L)$ the constant term is $\mathrm{CT}f(g)=\int f(u(q)g)\,d\nu(q)$ over $q\in\mathbb{A}_L$ with $u(q)=\begin{pmatrix}1&q\\0&1\end{pmatrix}$ and $\nu$ the conditioning of the adelic additive Haar measure on the adelic box of $L$ (the measure supplied by the carrier data built from $\Phi_L$, the level-one subgroups intersected with the finite-adelic subgroup, and the Hecke generators); here $f_{\mathcal B}(y)=\sum_{\delta}\varphi(x^{-1}\iota(\delta)\sigma_D(y))$ over $\delta$ with $\delta_{10}=0$ and $N_{L/K}(\delta_{00}/\delta_{11})\neq 1$, and $f_t(y)$ is the same sum over $\delta$ with $\delta_{10}=0$ and $\delta\in I(t)$.
--
--   This is the regrouping step for the hyperbolic contribution in the twisted (base-change) trace formula for $\mathrm{GL}_2$ over a cyclic extension: after folding over the centre and subtracting the truncating constant term, the whole hyperbolic term is a finite sum of the terms attached to those $\sigma$-conjugacy orbits $I(t)$ that meet the support of the test function. It feeds the two theorems that evaluate this expression as a sum of orbital and weighted orbital integrals for factorisable test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport.lean

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

theorem AutomorphicForm.setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (hΔcov : {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (Δφ : Finset (GL (Fin 2) L)) (hΔφsub : (↑Δφ : Set (GL (Fin 2) L)) ⊆ Δ)
    (hΔφ : ∀ t ∈ Δ, t ∉ Δφ → ∀ (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (R : ℝ) (x : AdelicGL2 (𝓞 L) L) :
    (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
    γ ∈ AutomorphicForm.hyperbolicCell K ∧
    LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (@AutomorphicForm.constantTerm _
    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
    (fun t => AutomorphicForm.unipotentGL2 t)
    (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
    (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) x =
      ∑ t ∈ Δφ, (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
      (@AutomorphicForm.constantTerm _
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
      (fun t => AutomorphicForm.unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}},
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
      (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) x := by sorry
