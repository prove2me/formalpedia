-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
-- name    : AutomorphicForm.TwistedBruhat.apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9b7f2104-818a-5fee-955e-e3deb4eb014a
-- title:
--   Vanishing of the twisted unipotent term off the saturated set
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $D$ be an idèle Galois descent datum for $L/K$ — a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, continuous and compatible with $L \to \mathbb{A}_L$ — and let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau$ lies in the group of integer powers of $\sigma$. Let $S_L$ be a finite set of primes of $\mathcal{O}_L$ containing every $w$ with $\mathrm{ramificationIdx}'$ of $w$ over its prime of $\mathcal{O}_K$ different from $1$; let $S, T$ be finite sets of primes of $\mathcal{O}_K$ with no prime of $S_L$ lying over a member of $T$; let $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adèles of $L$ and $\varphi_S$ a family of functions on $\mathrm{GL}_2(L \otimes_K K_v)$ be given; for each $v$ fix an extension $w_v$ to $\mathcal{O}_L$, a natural number $n_v$, elements $rT_v(0),\dots$ and $z_v$ of $\mathrm{GL}_2(L_{w_v})$, and naturals $k_v, j_v$. Assume $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$, $\varphi_f$ satisfy `IsSemiLocalFactorization` at $S \cup T$: $\varphi_a$ is smooth in the matrix entries with compact support, $\varphi_f$ is locally constant with compact support, each local factor at $v \in S \cup T$ is locally constant with compact support, $\varphi_f(h) = \prod_{v \in S \cup T}$ of the local factors applied to the semi-local components of $h$ whenever all components off $S \cup T$ lie in the semi-local integral set, $\varphi_f(h) = 0$ as soon as some component off $S \cup T$ fails to, and $\varphi(g)$ is the product of $\varphi_a$ on the archimedean part and $\varphi_f$ on the finite part; the local factor used at $v \in T$ is $x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)}$ of the indicator of the semi-local integral set evaluated at the inverse of the semi-local component of the local embedding at $w_v$ of $\bigl(\prod_m rT_v(\iota\, m)\bigr) z_v^{\,j_v}$ times $x$, and $\varphi_S\, v$ at $v \notin T$. Finally let $S_\tau$ be a finite set of primes of $\mathcal{O}_K$ characterised by: $v \in S_\tau$ exactly when either $v \in S$ and $v \notin T$, or some $w$ over $v$ has $\mathrm{ramificationIdx}'$ different from $1$. Then for every unit idèle $t$ of $L$ which is not saturated for $S_\tau$, i.e. for which some $v \notin S_\tau$ has the semi-local component of $t$ at $v$ outside the product of the integral units with the image of the units of $L$, for every $k$ in the adelic maximal compact subgroup (finite part in the integral level-zero subgroup, archimedean components row isometries at all infinite places), every unit idèle $\zeta$ and every adèle $w$, one has $$\varphi\bigl(k^{-1}\, n(w\,t^{-1})\, \mathrm{diag}(\sigma_D(t)\,t^{-1}, 1)\, \mathrm{scalar}(\sigma_D(\zeta))\, \sigma_D(k)\bigr) = 0,$$ where $\sigma_D$ denotes the action of $\sigma$ through $D$ on unit idèles and, entrywise, on $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   This is the unramified local vanishing statement for the twisted unipotent term: at a place outside $S_\tau$ the test function's local factor is supported on integral matrices, which forces the diagonal twist $\sigma_D(t)t^{-1}$ to be integral above $v$ and hence $t$ to be saturated at $v$. It feeds the evaluation of the twisted Bruhat contribution in [`AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2`](thm.html#AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram.lean

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
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.TwistedBruhat.apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfac : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1) :
    ∀ t : (AdeleRing (𝓞 L) L)ˣ, t ∉ AutomorphicForm.TransversalMeasure.saturated K L Sτ →
      ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0 := by sorry
