-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
-- name    : AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e646a7e0-b310-59fc-b3a0-84a6ad187cdd
-- title:
--   Uniform bound for twisted orbital integrals of one translate
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\nu_{Z_L}$ be a Haar measure on the idele units $(\mathbb{A}_L)^\times$, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, continuous and compatible with $L \to \mathbb{A}_L$), and let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$. Fix a finite set $S$ of finite places of $K$, a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, and functions $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for each finite place $v$ of $K$. Let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which $\sigma$ acting on $h$ via $D$ times $h^{-1}$ is central, and let $\mu_H$ be a right-invariant Haar measure on $H$. Let $\Delta \subseteq \mathrm{GL}_2(L)$ be a set each of whose members $t$ is diagonal with $N_{L/K}(t_{00}/t_{11}) \neq 1$, and such that distinct $t, t' \in \Delta$ have disjoint $\sigma$-twisted conjugacy classes modulo the centre, i.e. the sets $\{\delta : \exists g,\ t^{-1} g^{-1} \delta\, \sigma(g) \in Z(\mathrm{GL}_2(L))\}$ are disjoint. Then for every finite set $T$ of finite places of $K$ and every choice $w_v$ of a place of $L$ above each $v$ there is a real $C \geq 0$ with the following property. For every family of local elements $\rho_v \in \mathrm{GL}_2(L_{w_v})$, every $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that $\varphi$, $\varphi_a$, $\varphi_f$ form a semi-local factorisation relative to $S \cup T$ with local data given at $v \in T$ by the indicator of the integral set $\{x : x, x^{-1}$ have entries in the image of the integers of $L \otimes_K K_v\}$ translated by the inverse of the semi-local component at $v$ of the image of $\rho_v$ under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), and by $\varphi_{S,v}$ for $v \notin T$ — that is, $\varphi_a$ is smooth of compact support in the archimedean matrix entries, $\varphi_f$ is locally constant of compact support, the local data at places of $S \cup T$ are locally constant of compact support, $\varphi_f$ equals the product of the local data over $S \cup T$ when all semi-local components outside $S \cup T$ are integral and vanishes when some component outside is not, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$ — and for every finite $\Delta_\varphi \subseteq \Delta$, the sum over $t \in \Delta_\varphi$ of the two $[0,\infty]$-valued integrals over the orbit quotient of $\mathrm{GL}_2(\mathbb{A}_L)$ by $H$, taken with respect to the quotient measure built from the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\mu_H$, of the twisted orbital integrand $\int \lVert \varphi(q^{-1} t\, \sigma(zq)) \rVert \, \mathrm{d}\nu_{Z_L}(z)$ (with $t$ viewed in $\mathrm{GL}_2(\mathbb{A}_L)$, $z$ embedded as a central scalar, $\sigma$ acting via $D$, and $q$ represented by a chosen representative) and of the same integrand weighted by $\lvert -\log \mathrm{ht}(q) - \log \mathrm{ht}(wq) \rvert$, where $\mathrm{ht}$ is the adelic height (archimedean height times finite height) and $w$ is the adelic image of the antidiagonal Weyl element, is at most $C$.
--
--   This is the single-translate form of the bound on hyperbolic $\sigma$-twisted orbital integrals, together with their height-weighted companions, for a test function whose components at the places of $T$ are indicators of translated maximal compact sets: the bound is uniform in the translating local elements $\rho_v$ and in the finite subfamily $\Delta_\varphi$ of hyperbolic twisted classes. It is obtained by coset averaging against the double-coset statement and the corresponding double-coset bound, and it is in turn used for the bound over families of translates, [`AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates`](thm.html#AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_mul_prod_card_of_isSemiLocalFactorization_translates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate.lean

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

theorem AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate
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
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
            else φS v) →
      ∀ (Δφ : Finset (GL (Fin 2) L)), (↑Δφ ⊆ Δ) →
        (∑ t ∈ Δφ,
          ((∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) +
           (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) ≤
        ENNReal.ofReal C := by sorry
