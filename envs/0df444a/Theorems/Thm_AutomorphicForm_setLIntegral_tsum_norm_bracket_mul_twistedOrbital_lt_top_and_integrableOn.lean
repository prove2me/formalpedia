-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
-- name    : AutomorphicForm.setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/68449cbf-a220-5059-9cd7-0ab3f43bca06
-- title:
--   Integrability of one truncated twisted hyperbolic class sum
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals, and let $\Phi_L$ be a set of points of $\mathrm{GL}_2(\mathbb{A}_L)$ on which no hypothesis is imposed. Fix a Haar measure $\nu_{ZL}$ on the idele units $(\mathbb{A}_L)^\times$ (with its Borel structure) and a set $\Omega_L$ that is a fundamental domain for the image of $L^\times$ in $(\mathbb{A}_L)^\times$ with respect to $\nu_{ZL}$. Let $D$ be an idele Galois descent datum for $L/K$, that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous and compatible with $\tau\mapsto\tau$ on $L$, and let $\sigma$ be an element such that every $\tau\in\mathrm{Gal}(L/K)$ lies in $\langle\sigma\rangle^{\mathbb{Z}}$. Let $\xi_L$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$, continuous as a complex-valued function and trivial on the principal ideles. Let $c,u,d_1,d_2$ be reals with $c>0$, let $T_c$ be compact, and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ satisfy: $\Phi_0$ is contained in the union of the right translates $X\cdot y$, $y\in T_c$, of the centre-cut Siegel set $X$ of parameters $c,u,d_1,d_2$ (those $g$ whose finite part is integral, with $c\le$ the local height, $\mathrm{xWindowSq}\le u^2$ and archimedean determinant norm in $[d_1,d_2]$ at every infinite place); $\Phi_0$ lies in the slab where the idele norm of $\det g$, defined by the distributive Haar character, belongs to $[\alpha,\beta]$; and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on the adelic Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that slab. Let $\delta_0\in\mathrm{GL}_2(L)$ have vanishing off-diagonal entries and satisfy $N_{L/K}((\delta_0)_{00}/(\delta_0)_{11})\ne 1$; let $I$ be the set of $\delta$ for which some $g$ makes $\delta_0^{-1}g^{-1}\delta\,\sigma(g)$ central, and let $\Lambda$ be the subgroup of those $\gamma$ with $\delta_0^{-1}\gamma\delta_0\sigma(\gamma)^{-1}$ central. Let $r:\iota\to\mathrm{GL}_2(L)$, with $\iota$ countable, pick exactly one representative of each coset $r_i\Lambda$, i.e. for every $\gamma$ there is a unique $i$ with $r_i^{-1}\gamma\in\Lambda$. Finally let $\varphi$ be continuous with compact support on $\mathrm{GL}_2(\mathbb{A}_L)$ and $R$ real. Writing $y_i=\iota(r_i)^{-1}x$ for the image $\iota$ of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$, $b_R(y)=1-\mathbf{1}[e^R<\mathrm{H}(y)]-\mathbf{1}[e^R<\mathrm{H}(wy)]$ with $\mathrm{H}$ the adelic height (product of the archimedean and finite heights) and $w$ the adelic image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and $F(y)=\int\xi_L(z)\,\varphi\big(y^{-1}\iota(\delta_0)\,\sigma_D(z\cdot y)\big)\,d\nu_{ZL}(z)$ where $\sigma_D$ is the action of $\sigma$ through $D$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $z$ is embedded as the central scalar matrix, the conclusion is twofold: the integral over $\Phi_0$ of $\sum_i\lVert b_R(y_i)F(y_i)\rVert$ against the adelic Haar measure is finite, and $x\mapsto\sum_i b_R(y_i)F(y_i)$ is integrable on $\Phi_0$ for that measure.
--
--   This is the absolute-convergence statement for a single twisted hyperbolic conjugacy class in the truncated twisted trace formula for $\mathrm{GL}(2)$ over a cyclic extension, the truncation being the Arthur-type bracket $b_R$ built from the adelic height and its Weyl translate; the regularity condition $N_{L/K}((\delta_0)_{00}/(\delta_0)_{11})\ne1$ makes the twisted centraliser $\Lambda$ of $\delta_0$ the expected one. It is stated for every $R$ and without assuming $\sigma$-invariance or unitarity of $\xi_L$, and is used by [`AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn), the class-by-class regrouping of the hyperbolic term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn.lean

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

theorem AutomorphicForm.setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ) :
    (∫⁻ x in Φ₀, ∑' i, ‖(1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) < ⊤ ∧
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
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
