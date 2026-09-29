-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
-- name    : AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a4c17879-fbc4-5b90-9bf9-af220d78c0b5
-- title:
--   Combined orbital bound for Hecke double-coset test functions
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\nu_{Z,L}$ be a Haar measure on the idele units $(\mathbb{A}_L)^\times$, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $L \to \mathbb{A}_L$ and continuous), and let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the group of integral powers of $\sigma$. Fix a finite set $S$ of finite places of $K$, a function $\varphi_a$ on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ and functions $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$. Let $H \le \mathrm{GL}_2(\mathbb{A}_L)$ be a closed subgroup consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which $\mathrm{sigmaAdelicAct}(h) \cdot h^{-1}$ is central, and let $\mu_H$ be a right-invariant Haar measure on $H$. Let $\Delta \subseteq \mathrm{GL}_2(L)$ be a set of elements $t$ that are diagonal and satisfy $N_{L/K}(t_{00}/t_{11}) \neq 1$, and such that distinct $t, t' \in \Delta$ have disjoint $\sigma$-twisted classes, where the class of $t$ is $\{\delta : \exists g,\ t^{-1} g^{-1} \delta\, \sigma(g) \text{ is central}\}$. Then for every finite set $T$ of finite places of $K$ and every choice $w_v \mid v$ of an extension to $\mathcal{O}_L$ there are $C \ge 0$ and $A \in \mathbb{N}$ with the following property. For all local elements $\rho_v \in \mathrm{GL}_2(L_{w_v})$ and all $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $\varphi_f$ on $\mathrm{GL}_2(\mathbb{A}_{L,f})$ such that $\varphi$ admits the semi-local factorisation at $S \cup T$ with archimedean factor $\varphi_a$, finite factor $\varphi_f$, and local factors equal at $v \in T$ to the indicator with value $1$ of the double coset $\mathcal{K}_v \cdot \{a_v\} \cdot \mathcal{K}_v$, where $\mathcal{K}_v$ is the semi-local integral set of $\mathrm{GL}_2(L \otimes_K K_v)$ and $a_v$ is the semi-local component at $v$ of the image of $\rho_v$ under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), and to $\varphi_{S,v}$ at the remaining places — and for every finite $\Delta_\varphi \subseteq \Delta$, the sum over $t \in \Delta_\varphi$ of the twisted orbital integral $\int_{H \backslash \mathrm{GL}_2(\mathbb{A}_L)} \int_{(\mathbb{A}_L)^\times} \lVert \varphi(q^{-1} t\, \mathrm{sigmaAdelicAct}(z q)) \rVert\, d\nu_{Z,L}\, dq$ plus the same integral weighted by $\lvert -\log h(q) - \log h(wq) \rvert$, with $h$ the adelic height, $w$ the image in $\mathrm{GL}_2(\mathbb{A}_L)$ of the Weyl element $\begin{pmatrix} 0&1\\1&0\end{pmatrix}$, and the quotient measure the [`HaarQuotient.measure`](def/HaarQuotient.html#L28) built from the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$, $H$ and $\mu_H$ (the integrands evaluated at chosen representatives $q$ of classes), is at most $$C \prod_{v \in T} \mu_v(\mathcal{K}_v a_v \mathcal{K}_v)^{1/2}\bigl(1 + \log \mu_v(\mathcal{K}_v a_v \mathcal{K}_v)\bigr)^A,$$ where $\mu_v$ is the semi-local Haar measure normalised by $\mu_v(\mathcal{K}_v) = 1$.
--
--   This is the combined bound, plain plus logarithmically weighted, for the hyperbolic twisted orbital integrals of a test function whose components at the places of $T$ are Hecke double-coset indicators: the total is controlled by the square root of the coset volume times a fixed power of its logarithm. It is obtained from the separate bounds for the plain orbital integrals, for the weighted ones, and for the number of contributing twisted classes, and feeds the statement [`AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate`](thm.html#AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate) in the trace-formula comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure.lean

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

theorem AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_doubleCoset_le_mul_prod_rpow_measure
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
        ENNReal.ofReal (C * ∏ v ∈ T,
          ((AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A)) := by sorry
