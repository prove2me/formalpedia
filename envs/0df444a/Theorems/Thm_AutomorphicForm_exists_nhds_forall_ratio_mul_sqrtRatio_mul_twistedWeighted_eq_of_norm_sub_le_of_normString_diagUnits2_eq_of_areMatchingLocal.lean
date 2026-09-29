-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
-- name    : AutomorphicForm.exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/5a384193-edcf-50b7-b207-dfd714e6cf8b
-- title:
--   Near t=1, normalised twisted weighted values agree on cells
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$, assume $[L:K]$ is prime, and let $v$ be a nonzero prime of $\mathcal{O}_K$. Let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ and $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be locally constant of compact support, and assume $\varphi$ and $f$ match locally at $v$ relative to $\sigma$, in the sense of [`AutomorphicForm.AreMatchingOn`](def/AutomorphicForm_TwistedOrbital.html#L324) for the semi-local and local Haar measures. Then there are a neighbourhood $U$ of $1$ in $K_v^{\times}$ and a real $\rho > 0$ with the following property. Let $a, a', t, t' \in K_v^{\times}$ satisfy $t \in U$, $\|a' - a\| \le \rho\|a\|$, $\|t' - t\| \le \rho\|1 - t\|$ and $t, t' \neq 1$. Let $\alpha, \beta \in (L \otimes_K K_v)^{\times}$ be such that the twisted norm string $\prod_{i<[L:K]} \sigma^i(\mathrm{diag}(\alpha,\beta))$ (the product of the iterates of the map [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) induced by $\sigma$) equals the image of $\mathrm{diag}(a, at)$ under the base-change homomorphism [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71); let $\tau'$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser of $\mathrm{diag}(\alpha,\beta)$, normalised so that the set of its elements lying in [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136) (matrices in $\mathrm{GL}_2(L \otimes_K K_v)$ with entries of themselves and of their inverses in the semi-local integers) has measure $1$; and let $J' \in \mathbb{C}$ be a twisted weighted orbital integral of $\varphi$ at $\mathrm{diag}(\alpha,\beta)$ with respect to $\tau'$, the semi-local Haar measure and the semi-local weight. Let $\alpha', \beta', \tau'', J''$ satisfy the same conditions with $\mathrm{diag}(a', a't')$ in place of $\mathrm{diag}(a, at)$. Then $$\|1 - t\|\,\bigl(\|a\|/\|at\|\bigr)^{1/2} J' = \|1 - t'\|\,\bigl(\|a'\|/\|a't'\|\bigr)^{1/2} J'',$$ the real factors being [`AutomorphicForm.LocalWeightedOrbital.ratio`](def/AutomorphicForm_LocalWeightedOrbital.html#L77) times [`AutomorphicForm.LocalWeightedOrbital.sqrtRatio`](def/AutomorphicForm_LocalWeightedOrbital.html#L80) for the norm on $K_v$, coerced into $\mathbb{C}$.
--
--   This is the local radial statement that the normalised twisted weighted orbital integral at a regular diagonal element $\mathrm{diag}(a,at)$ depends only on the cell of $(a,t)$ near the singular point $t = 1$, so that the twisted side of the comparison at $v$ is constant along cells. It is the constancy clause used in the combined local matching statement [`AutomorphicForm.exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal`](thm.html#AutomorphicForm.exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal), which feeds the local base-change comparison for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean

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

theorem AutomorphicForm.exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)  :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
        t ≠ 1 → t' ≠ 1 →
        (∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
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
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')) →
            ∀ (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β'))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β'))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β')) τ'' →
              τ'' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J'' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α' β') τ'' φ J'' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') : ℝ) : ℂ) * J'') := by sorry
