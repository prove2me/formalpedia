-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_orbital_le_sum_and_weightedOrbital_le_sum_of_isSemiLocalFactorization_of_eq_sum
-- name    : AutomorphicForm.lintegral_orbital_le_sum_and_weightedOrbital_le_sum_of_isSemiLocalFactorization_of_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/584aa2f4-9e27-59e9-8f03-8da071effcf6
-- title:
--   Subadditivity of twisted orbital and height-weighted orbital integrals
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\nu_{Z_L}$ be a Haar measure on the group of ideles $(\mathbb{A}_L)^{\times}$ of $L$, and let $D$ be an idele Galois descent datum for $L/K$, that is, a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ by continuous automorphisms extending the action on $L$. Let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, let $S$ be a finite set of finite places of $K$, and let $\varphi_a$ and $(\varphi_S(v))_v$ be functions on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ and on the groups $\mathrm{GL}_2(L \otimes_K K_v)$ (these two data do not occur in the conclusion). Let $H$ be a closed subgroup of $G = \mathrm{GL}_2(\mathbb{A}_L)$ consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which $\sigma_D(h)h^{-1}$ is central, equipped with a right-invariant Haar measure $\mu_H$, where $\sigma_D$ denotes the entrywise action of $D(\sigma)$. Let $\Delta \subseteq \mathrm{GL}_2(L)$ be a set each of whose elements $t$ is diagonal with $N_{L/K}(t_{00}/t_{11}) \neq 1$, and such that for distinct $t,t' \in \Delta$ the sets $\{\delta : \exists g,\ t^{-1}g^{-1}\delta\,\sigma(g) \text{ central}\}$ and the analogous set for $t'$ are disjoint. Then for every finite set $T$ of finite places of $K$, every finite index type $J$, every family $\varphi_j$ $(j \in J)$ of functions $G \to \mathbb{C}$ each admitting a semi-local factorisation at $S \cup T$ — i.e. factors $\psi_a$ (smooth in the mixed-space matrix entries, compactly supported), $\psi_f$ (locally constant, compactly supported) and $\psi_S(v)$ (locally constant, compactly supported for $v \in S \cup T$) with $\psi_f$ equal to $\prod_{v \in S \cup T}\psi_S(v)$ of the semi-local components when all components outside $S \cup T$ are integral, zero otherwise, and $\varphi_j(g) = \psi_a(g_\infty)\psi_f(g_f)$ — and every $\varphi$ with $\varphi = \sum_j \varphi_j$ pointwise, the following hold for each $t \in \Delta$. Writing $Z_{t,\psi}(y) = \int^{-} \|\psi(y^{-1} t\, \sigma_D(c(z)y))\|\,d\nu_{Z_L}(z)$ with $c$ the central scalar embedding and $y$ a chosen representative of a class in the quotient of $G$ by the orbit relation of $H$, endowed with the quotient measure built from the adelic Haar measure on $G$ and $\mu_H$: the integral of $Z_{t,\varphi}$ over that quotient is at most $\sum_j$ of the integral of $Z_{t,\varphi_j}$, and likewise after inserting the weight $\bigl|-\log \mathrm{ht}(y) - \log \mathrm{ht}(w\,y)\bigr|$, where $\mathrm{ht}$ is the adelic height and $w$ the image in $G$ of the Weyl element of $\mathrm{GL}_2(L)$.
--
--   This records subadditivity, in the $\mathbb{R}_{\ge 0}^{\infty}$-valued sense, of the two class-sum terms attached to an element $t$ of the twisted-conjugacy parameter set $\Delta$ in the twisted $\mathrm{GL}_2$ trace formula over a cyclic extension $L/K$: the orbital term and its height-weighted companion. It is used in the derivation of the uniform bound [`AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates`](thm.html#AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates), where a test function is decomposed into a finite family of semi-locally factorised translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_orbital_le_sum_and_weightedOrbital_le_sum_of_isSemiLocalFactorization_of_eq_sum.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.lintegral_orbital_le_sum_and_weightedOrbital_le_sum_of_isSemiLocalFactorization_of_eq_sum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) {J : Type} [Fintype J]
      (φs : J → AdelicGL2 (𝓞 L) L → ℂ) (φ : AdelicGL2 (𝓞 L) L → ℂ),
      (∀ j : J, ∃ (ψa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (ψf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
          (ψS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
          IsSemiLocalFactorization K L (S ∪ T) (φs j) ψa ψf ψS) →
      (∀ x : AdelicGL2 (𝓞 L) L, φ x = ∑ j : J, φs j x) →
      ∀ t ∈ Δ,
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≤
          ∑ j : J, (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φs j (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ∧
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≤
          ∑ j : J, (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φs j (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) := by sorry
