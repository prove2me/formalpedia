-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal
-- name    : AutomorphicForm.TwistedBruhat.ae_mem_structuredBox_of_transversal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/bda121b7-6774-5a3b-a84a-6ee4d5cf4c66
-- title:
--   Almost every idele lies in the structured box
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $S_\tau$ be a finite set of finite places of $K$ (height-one primes of $\mathcal O_K$), let $n\in\mathbb N$, $c:\mathrm{Fin}\,n\to\mathbb R$, and for each index $j$ let $\tau_j$ be a measure on the idele group $(\mathbb A_L)^\times$ with its Borel structure, $\tau^{\mathrm{fin}}_{j,v}$ a measure on $(L\otimes_K K_v)^\times$ for each finite place $v$ of $K$, $\tau^{\mathrm{arch}}_{j,v}$ a measure on $\bigl(\prod_{w\mid v}L_w\bigr)^\times$ for each infinite place $v$, and $\pi_{j,v}\in (L\otimes_K K_v)^\times$. Assume: $c_j>0$; $\tau_j$ gives mass zero to the set where the idele norm (the distributive Haar character of translation on $\mathbb A_L$) differs from $c_j$; $\tau_j$ is finite on compacts; $\tau_j$ gives mass zero to the complement of `saturated K L Sτ`, the set of $t$ whose semi-local component at each $v\notin S_\tau$ lies in `integralUnits` times the range of `includeUnits`; for $v\notin S_\tau$, $\tau^{\mathrm{fin}}_{j,v}$ is a Haar measure restricted to and normalised on the integral units $U_v$ (the unit subgroup of the image of $\mathcal O_L\otimes_{\mathcal O_K}\mathcal O_{K_v}$), with mass $0$ off $U_v$ and mass $1$ on $U_v$; for $v\in S_\tau$, $\tau^{\mathrm{fin}}_{j,v}$ is the image under $x\mapsto \pi_{j,v}x$ of a Haar measure on the norm-one units $N^1_v$ (kernel of $\mathrm{Valued.v}\circ \mathrm{Algebra.norm}$), pushed forward along the inclusion; each $\tau^{\mathrm{arch}}_{j,v}$ is the pushforward of a Haar measure on the archimedean norm-one units $N^1_{v,\infty}$ (kernel of the absolute value of the norm to $K_v$); and, for every finite $S_f\supseteq S_\tau$ and all $\mathbb R_{\ge0}^\infty$-valued test functions $f_v$ ($v\in S_f$ measurable) and $g_v$ (measurable), the lower integral over $\tau_j$ of $\bigl(\prod_{v\mid\infty}g_v(t_v)\bigr)\bigl(\prod_{v\in S_f}f_v(t_v)\bigr)$ times the indicator of $\{t: t_v\in U_v\ \forall v\notin S_f\}$ equals $\prod_{v\mid\infty}\int g_v\,d\tau^{\mathrm{arch}}_{j,v}\cdot\prod_{v\in S_f}\int f_v\,d\tau^{\mathrm{fin}}_{j,v}$, where $t_v$ denotes the semi-local component of $t$ above $v$. Then for each $j$ and $\tau_j$-almost every idele $t$: $t_v\in N^1_{v,\infty}$ for all infinite $v$, $\pi_{j,v}^{-1}t_v\in N^1_v$ for all $v\in S_\tau$, and $t_v\in U_v$ for all finite $v\notin S_\tau$.
--
--   This is the torus-confinement step for transversal measures on the idele group: it converts the local descriptions and the product formula for test functions into the assertion that the measure is carried by a single structured box cut out by norm-one and integrality conditions at every place of $K$. It is used in the twisted Bruhat results [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram) and [`AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal.lean

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

theorem AutomorphicForm.TwistedBruhat.ae_mem_structuredBox_of_transversal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

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
    (j : Fin n) :
    ∀ᵐ t ∂(τ j),
      (∀ v : InfinitePlace K,
          AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.archNormOneUnits K L v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ →
          (πs j v)⁻¹ * AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
            AutomorphicForm.TransversalMeasure.normOneUnits K L v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ →
          AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v) := by sorry
