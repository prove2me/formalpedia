-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
-- name    : AutomorphicForm.exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/c291999c-d930-57e8-8f1e-f9da8c4eb6bb
-- title:
--   Counting hyperbolic σ-classes contributing to a double-coset orbital integral
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\nu_{Z_L}$ be a Haar measure on $(\mathbb{A}_L)^\times$, let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the continuous ring automorphisms of $\mathbb{A}_L$ extending the action on $L$, and let $\sigma$ be an element such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$. Fix a finite set $S$ of finite places of $K$, a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles, functions $\varphi_{S,v}$ on each $\mathrm{GL}_2(L \otimes_K K_v)$, a closed subgroup $H \le \mathrm{GL}_2(\mathbb{A}_L)$ consisting exactly of the $h$ with vanishing $(1,0)$ and $(0,1)$ entries such that $\sigma(h)h^{-1}$ is central (where $\sigma$ acts through [`AutomorphicForm.sigmaAdelicAct`](def/AutomorphicForm_SigmaAdelicAction.html#L14)), and a right-invariant Haar measure $\mu_H$ on $H$. Let $\Delta \subseteq \mathrm{GL}_2(L)$ be a set each of whose elements $t$ has vanishing $(1,0)$ and $(0,1)$ entries and satisfies $N_{L/K}(t_{00}/t_{11}) \neq 1$, and such that for distinct $t,t' \in \Delta$ the sets $\{\delta : \exists g,\ t^{-1}g^{-1}\delta\,\sigma(g) \text{ central}\}$ and the corresponding set for $t'$ are disjoint. Then for every finite set $T$ of finite places of $K$ and every choice of a place $w_v$ of $L$ above each $v$ there are $C \ge 0$ and $A \in \mathbb{N}$ with the following property. Let $\rho_v \in \mathrm{GL}_2(L_{w_v})$ for each $v$, and let $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles satisfy `IsSemiLocalFactorization` for $S \cup T$: $\varphi_a$ is an archimedean test factor, $\varphi_f$ a finite test factor, each semi-local factor at a place of $S \cup T$ is a semi-local test function, $\varphi_f$ vanishes at $h$ unless every semi-local component outside $S \cup T$ lies in the integral set and otherwise equals the product over $S \cup T$ of the semi-local factors evaluated at the components, and $\varphi(g)$ is the product of $\varphi_a$ at the archimedean part of $g$ and $\varphi_f$ at its finite part — where the semi-local factor at $v \in T$ is the indicator of the double coset $\mathcal{K}_v \cdot \{\text{component at } v \text{ of the image of } \rho_v\} \cdot \mathcal{K}_v$, $\mathcal{K}_v$ being `semiLocalIntegralSet`, and at $v \notin T$ is $\varphi_{S,v}$. Then every finite $\Delta_\varphi \subseteq \Delta$ such that for each $t \in \Delta_\varphi$ the iterated integral over the quotient of $\mathrm{GL}_2(\mathbb{A}_L)$ by the $H$-orbit relation (with the measure built by [`HaarQuotient.measure`](def/HaarQuotient.html#L28) from the adelic Haar measure and $\mu_H$) of $\int \|\varphi(q^{-1} t\, \sigma(z q))\|\,d\nu_{Z_L}(z)$, with $q$ a chosen representative and $z$ ranging over central idelic scalars, is non-zero satisfies $$\#\Delta_\varphi \le C \prod_{v \in T} \bigl(1 + \log \mu'_v(\mathcal{K}_v \rho_v \mathcal{K}_v)\bigr)^A,$$ where $\mu'_v$ is [`AutomorphicForm.semiLocalHaar`](def/AutomorphicForm_TwistedOrbital.html#L169) on $\mathrm{GL}_2(L \otimes_K K_v)$.
--
--   This is the counting step in the geometric comparison for base change along $L/K$: it bounds, uniformly in the Hecke double-coset test function chosen at the places of $T$, the number of regular diagonal $\sigma$-twisted classes whose orbital contribution is non-zero, the bound being a power of the logarithm of the double-coset volumes. It feeds the estimate [`AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure), and rests on the norm-ratio injectivity statement for $\sigma$-classes together with a lattice-point count for $S$-units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero.lean

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

theorem AutomorphicForm.exists_forall_card_le_mul_prod_pow_log_measure_of_lintegral_orbital_doubleCoset_ne_zero
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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (Δφ : Finset (GL (Fin 2) L)), (↑Δφ ⊆ Δ) →
        (∀ t ∈ Δφ,
          (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ≠ 0) →
        (Δφ.card : ℝ) ≤ C * ∏ v ∈ T,
          ((1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A) := by sorry
