-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn
-- name    : AutomorphicForm.exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/57824db9-ed0b-596d-aa46-1206ed30daca
-- title:
--   Vanishing of hyperbolic terms for non-σ-invariant ξ_L
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals, let $\Phi_L$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_L)$, let $\nu_{Z L}$ be a Haar measure on $\mathbb{A}_L^\times$ (with the Borel structure) and $\Omega_L$ a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z L}$. Let $D$ be an idele Galois descent datum for $L/K$, that is, a continuous action of $\mathrm{Gal}(L/K)$ on $\mathbb{A}_L$ by ring automorphisms compatible with $L\hookrightarrow\mathbb{A}_L$, and let $\sigma$ generate $\mathrm{Gal}(L/K)$, in the sense that every $\tau$ lies in the subgroup of integral powers of $\sigma$. Let $\xi_L$ be a homomorphism from the full unit group $\mathbb{A}_L^\times$ (presented as the top subgroup) to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function and trivial on the image of $L^\times$. Let $c>0$, $u,d_1,d_2$ be reals, $T_c$ compact, and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ be contained in the union of the right translates by elements of $T_c$ of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (integral finite part, local heights at least $c$, window coordinate squares at most $u^2$, archimedean determinant norms in $[d_1,d_2]$), contained in the slab where the idelic norm of the determinant lies in $[\alpha,\beta]$, and a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on that slab with respect to the adelic Haar measure restricted to it. Let $H$ be a closed subgroup consisting exactly of those $h$ with vanishing $(1,0)$ and $(0,1)$ entries such that $\sigma_D(h)h^{-1}$ is central, equipped with a right-invariant Haar measure $\mu_H$. Assume $\xi_L$ is not $\sigma$-invariant: it is not the case that $\xi_L(D.\mathrm{unitsAct}\,\sigma\, z)=\xi_L(z)$ for all ideles $z$. Let $\delta_0\in\mathrm{GL}_2(L)$ have vanishing off-diagonal entries with $N_{L/K}((\delta_0)_{00}/(\delta_0)_{11})\neq 1$; let $I$ be the set of $\delta$ for which some $g$ makes $\delta_0^{-1}g^{-1}\delta\,\sigma(g)$ central, and $\Lambda$ the subgroup of $\gamma$ with $\delta_0^{-1}\gamma\delta_0\sigma(\gamma)^{-1}$ central; let $r:\iota\to\mathrm{GL}_2(L)$, with $\iota$ countable, be such that each $\gamma$ satisfies $(r\,i)^{-1}\gamma\in\Lambda$ for a unique $i$. Finally let $\varphi$ be a factorizable test function, i.e. $\varphi(g)=f_a(g_\infty)f_f(g_{\mathrm{fin}})$ with $f_a$ smooth in the matrix entries and compactly supported and $f_f$ locally constant and compactly supported. Then there is $R_1\in\mathbb{R}$ such that for every $R\ge R_1$ the integral over $\Phi_0$, against the adelic Haar measure, of the sum over $i$ of $\bigl(1-\mathbf 1[\,e^R<\mathrm{ht}(y_i)\,]-\mathbf 1[\,e^R<\mathrm{ht}(w\,y_i)\,]\bigr)\cdot\int \xi_L(z)\,\varphi\bigl(y_i^{-1}\,\delta_0\,\sigma_D(z\cdot y_i)\bigr)\,d\nu_{ZL}(z)$, where $y_i=(r\,i)^{-1}x$ in $\mathrm{GL}_2(\mathbb{A}_L)$ (images of $r\,i$ and $\delta_0$ under $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$), $w$ is the adelic Weyl element, $z$ acts through the central scalar embedding, and $\mathrm{ht}$ is the adelic height, equals $0$.
--
--   This is the vanishing branch for a single $\sigma$-regular (hyperbolic) class in the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension: when the central character datum $\xi_L$ fails to be invariant under the Galois descent action, the truncated orbital contribution attached to a diagonal $\delta_0$ with $N_{L/K}((\delta_0)_{00}/(\delta_0)_{11})\neq1$ vanishes for all sufficiently large truncation parameters. It feeds the dichotomy statement [`AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn) and the evaluation [`AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn`](thm.html#AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn
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

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ¬ ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
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
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
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
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by sorry
