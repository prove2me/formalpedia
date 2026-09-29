-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
-- name    : AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b5356c68-2a4b-5dd9-9706-94f894caa7b9
-- title:
--   Bounded Galois ratio confines transversal ideles to a compact set
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ Galois, let $D$ be an idelic Galois descent datum for $L/K$ (a monoid homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$, compatible with the map from $L$ and continuous in each component), and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Fix a finite set $S_\tau$ of height-one primes of $\mathcal{O}_K$, an integer $n$, reals $c_j$, measures $\tau_j$ on $\mathbb{A}_L^\times$ (with its Borel structure), measures $\tau_{\mathrm{fin},j,v}$ on $(L\otimes_K K_v)^\times$ for each finite place $v$ of $K$, measures $\tau_{\mathrm{arch},j,v}$ on $\bigl(\prod_{w\mid v}L_w\bigr)^\times$ for each infinite place $v$ of $K$, and elements $\pi_{j,v}\in(L\otimes_K K_v)^\times$. Assume: $c_j>0$; $\tau_j$ gives measure zero to the set where the idele norm (the module of $t$, i.e. the distributive Haar character of $\mathbb{A}_L$ at $t$) differs from $c_j$; each $\tau_j$ is finite on compacts; $\tau_j$ vanishes on the complement of the saturated set, consisting of those $t$ whose semi-local component at each $v\notin S_\tau$ lies in `saturatedUnits K L v`; for $v\notin S_\tau$, $\tau_{\mathrm{fin},j,v}$ is a Haar measure normalised and restricted to the integral units (the units of the image of $\mathcal{O}_L\otimes\mathcal{O}_{K_v}$), and that subgroup has measure $1$ and full complement-measure $0$; for $v\in S_\tau$, $\tau_{\mathrm{fin},j,v}$ is the image under $x\mapsto\pi_{j,v}x$ of the pushforward of a Haar measure on the norm-one units (kernel of $v$-valuation composed with the $K_v$-algebra norm); each $\tau_{\mathrm{arch},j,v}$ is the pushforward of a Haar measure on the archimedean norm-one units (kernel of the absolute value of the $K_v$-algebra norm); and, for every finite $S_f\supseteq S_\tau$ and all measurable $[0,\infty]$-valued local test functions, the $\tau_j$-integral of the product of the archimedean local functions, the local functions at places of $S_f$, and the indicator of integrality outside $S_f$, factors as the product of the local integrals against the $\tau_{\mathrm{arch},j,v}$ and $\tau_{\mathrm{fin},j,v}$. Then for every compact $C_d\subseteq\mathbb{A}_L^\times$ and every index $j$ there is a compact $C_t\subseteq\mathbb{A}_L^\times$ such that, for $\tau_j$-almost every $t$, if the Galois ratio $\sigma(t)\,t^{-1}$ (for the unit-group automorphism induced by $D$ at $\sigma$) lies in $C_d$, then $t\in C_t$.
--
--   This is the global compactness input for the torus variable in the twisted Bruhat decomposition: on each transversal piece $\tau_j$ of the idelic measure, boundedness of the Galois ratio $\sigma(t)/t$ confines $t$ to a compact set up to a null set, the idelic analogue of the compactness of the norm-one idele classes. It is used in bounding the unipotent twist contributions to the trace on fibres in the unramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram.lean

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
import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hgood : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v))
    (Cd : Set (AdeleRing (𝓞 L) L)ˣ) (hCd : IsCompact Cd) (j : Fin n) :
    ∃ Ct : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact Ct ∧
      ∀ᵐ t ∂(τ j), M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹ ∈ Cd → t ∈ Ct := by sorry
