-- Prove2me | Theorems.Thm_AutomorphicForm_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_normString_diagUnits2_eq_of_areMatchingLocal
-- name    : AutomorphicForm.ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_normString_diagUnits2_eq_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/99bef4e1-05be-5468-bda7-21ac767aaae3
-- title:
--   Lift-independence of twisted weighted orbital integrals at diag(a,at)
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the group is an integral power of $\sigma$, assume $[L:K]$ is prime, and let $v$ be a nonzero prime of $\mathcal{O}_K$, with completion $K_v$. Let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be locally constant with compact support, let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be locally constant with compact support, and assume $\varphi$ and $f$ match in the sense of [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386) (the matching relation for the semi-local and local Haar measures at $v$). The assertion is: for all units $a, t$ of $K_v$ with $t \neq 1$, and for any two pairs $\alpha, \beta$ and $\alpha', \beta'$ of units of $L \otimes_K K_v$ whose diagonal matrices $\delta = \mathrm{diag}(\alpha,\beta)$ and $\delta' = \mathrm{diag}(\alpha',\beta')$ satisfy `normString` $= \delta \cdot \sigma(\delta) \cdots \sigma^{[L:K]-1}(\delta) = \mathrm{diag}(a, at)$, the latter viewed in $\mathrm{GL}_2(L\otimes_K K_v)$ through the inclusion of the right tensor factor; and for any Borel Haar measures $\tau'$, $\tau''$ on the $\sigma$-twisted centralisers of $\delta$, $\delta'$ normalised so that the set of elements lying in the semi-local integral units set [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136) has measure $1$; and for any complex numbers $J'$, $J''$ satisfying the twisted weighted orbital integral relation [`AutomorphicForm.IsTwistedWeightedOrbitalIntegral`](def/AutomorphicForm_WeightedOrbitalRelation.html#L89) for $(\delta,\tau',\varphi)$ and $(\delta',\tau'',\varphi)$ respectively — one has $c \cdot J' = c \cdot J''$, where $c = \|1 - (at)a^{-1}\| \cdot \sqrt{\|a\|/\|at\|}$ is the normalising factor built from `ratio` and `sqrtRatio` for the $v$-adic absolute value. The proof visibly discards the primality hypothesis on $[L:K]$ and the data $f$ together with its test-function and matching hypotheses.
--
--   This records that the normalised twisted weighted orbital integral at a split regular diagonal element $\mathrm{diag}(a,at)$, $t \neq 1$, of $\mathrm{GL}_2(K_v)$ does not depend on the choice of exact diagonal $\sigma$-norm lift, on the mass-one Haar measure on the twisted centraliser, or on the particular value realising the twisted weighted relation. It feeds the germ/continuity statement for the local weighted comparison at $v$ used in the base-change trace identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_normString_diagUnits2_eq_of_areMatchingLocal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_normString_diagUnits2_eq_of_areMatchingLocal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)  :
    ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
      ∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ∀ α' β' : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α' β') =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β'))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β'))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β')) τ'' →
              τ'' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J'' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α' β') τ'' φ J'' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J'' := by sorry
