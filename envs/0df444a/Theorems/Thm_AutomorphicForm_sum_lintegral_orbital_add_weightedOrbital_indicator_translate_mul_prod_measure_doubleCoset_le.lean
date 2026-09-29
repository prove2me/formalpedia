-- Prove2me | Theorems.Thm_AutomorphicForm_sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
-- name    : AutomorphicForm.sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6fc6754e-bbea-5982-8cbb-2e094daa4fb1
-- title:
--   Double-coset volume bound for twisted orbital class sums
-- statement:
--   Let $L/K$ be a Galois extension of number fields, $\nu_{Z_L}$ a Haar measure on the idèle units $(\mathbb A_L)^\times$, and $D$ an idèle Galois descent datum for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$ which is continuous and extends the action on $L$; let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ is an integral power of $\sigma$. Fix a finite set $S$ of finite places of $K$, an archimedean factor $\varphi_a$ on $\mathrm{GL}_2(\mathbb A_{L,\infty})$ and semi-local factors $\varphi_{S,v}$ on $\mathrm{GL}_2(L\otimes_K K_v)$. Let $H \le \mathrm{GL}_2(\mathbb A_L)$ be a closed subgroup consisting exactly of those $h$ with vanishing $(1,0)$ and $(0,1)$ entries such that $\sigma_D(h)h^{-1}$ is central, equipped with a right-invariant Haar measure $\mu_H$. Let $\Delta \subseteq \mathrm{GL}_2(L)$ consist of diagonal elements $t$ with $N_{L/K}(t_{00}/t_{11}) \ne 1$, pairwise separated in the sense that for distinct $t,t' \in \Delta$ the sets $\{\delta : \exists g,\ t^{-1}(g^{-1}\delta\,\sigma(g)) \text{ central}\}$ and the corresponding set for $t'$ are disjoint. For a test function $\psi$ on $\mathrm{GL}_2(\mathbb A_L)$ and a finite $\Delta_\varphi$ write $\mathrm{cs}(\psi;\Delta_\varphi)$ for the sum over $t \in \Delta_\varphi$ of the two lower integrals over the quotient of $\mathrm{GL}_2(\mathbb A_L)$ by the $H$-orbit relation, taken with respect to the measure obtained by pushing forward the adelic Haar measure `adelicGLHaar` weighted by [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25), of (i) $\int^- \|\psi(q^{-1}\,t\,\sigma_D(z\,q))\|\,d\nu_{Z_L}(z)$, where $q$ is the chosen representative of the class, $t$ is viewed in $\mathrm{GL}_2(\mathbb A_L)$ and $z$ as the central scalar $\mathrm{diag}(z,z)$, and (ii) that same inner integral multiplied by $\bigl|-\log \mathrm{ht}(q) - \log \mathrm{ht}(w\,q)\bigr|$, with $\mathrm{ht}$ the adelic height and $w$ the adelic Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. The assertion is: for every finite set $T$ of finite places of $K$, every choice of a place $w_v$ of $L$ above each $v$, every $\rho_v \in \mathrm{GL}_2(L_{w_v})$, and every pair $(\varphi,\varphi_f)$ which is a semi-local factorisation over $S \cup T$ with archimedean factor $\varphi_a$, finite factor $\varphi_f$ and semi-local factors given at $v \in T$ by $x \mapsto \mathbf 1_{\mathcal K_v}(\tilde\rho_v^{-1} x)$ and by $\varphi_{S,v}$ otherwise — where $\mathcal K_v$ is the set of elements of $\mathrm{GL}_2(L \otimes_K K_v)$ integral together with their inverses, $\tilde\rho_v$ the image of $\rho_v$ under the local embedding into $\mathrm{GL}_2(\mathbb A_{L,f})$ followed by the semi-local component map, and the factorisation condition requires $\varphi_a$ smooth of compact support in the archimedean entries, $\varphi_f$ locally constant of compact support, each semi-local factor at $v \in S\cup T$ locally constant of compact support, $\varphi_f(h)$ equal to the product of the semi-local factors over $S \cup T$ when all components outside $S \cup T$ lie in $\mathcal K_{v}$ and zero otherwise, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_f)$ — and every pair $(\varphi',\varphi_f')$ which is such a factorisation with the same data except that the factor at $v \in T$ is the indicator of the double coset $\mathcal K_v \tilde\rho_v \mathcal K_v$, one has for every finite $\Delta_\varphi \subseteq \Delta$ $$\mathrm{cs}(\varphi;\Delta_\varphi)\cdot\prod_{v \in T}\mu_v\bigl(\mathcal K_v \tilde\rho_v \mathcal K_v\bigr) \le \mathrm{cs}(\varphi';\Delta_\varphi),$$ where $\mu_v$ is the Haar measure [`AutomorphicForm.semiLocalHaar`](def/AutomorphicForm_TwistedOrbital.html#L169) on $\mathrm{GL}_2(L\otimes_K K_v)$ normalised by $\mathcal K_v$.
--
--   This is the coset-averaging comparison step in the twisted orbital analysis: the class sum attached to a single left-translate of the unit coset at the places of $T$, multiplied by the number of left cosets in the corresponding double coset, is bounded by the class sum attached to the double-coset indicator. It is used by [`AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate`](thm.html#AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate), and it relies on the decomposition of $\mathcal K_v \tilde\rho_v \mathcal K_v$ into finitely many disjoint left cosets whose number equals its $\mathcal K_v$-normalised volume.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le.lean

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

theorem AutomorphicForm.sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ φa φf
        (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
          else φS v) →
    ∀ (φ' : AdelicGL2 (𝓞 L) L → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ' φa φf'
        (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} * semiLocalIntegralSet K L v).indicator
              (fun _ => (1 : ℂ)) x
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
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) *
        (∏ v ∈ T, AutomorphicForm.semiLocalHaar K L v
          (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} * semiLocalIntegralSet K L v)) ≤
      (∑ t ∈ Δφ,
          ((∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ' (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) +
           (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ' (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) := by sorry
