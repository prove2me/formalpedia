-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_localConditionsWeighted_trivial_coords
-- name    : Formalism.EigenvalueLevelCeiling.localConditionsWeighted_trivial_coords
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:56.304497+00:00
-- url     : https://prove2.me/theorems/5a44769e-305d-539e-bc58-2c42914b4fdd
-- title:
--   Eigenvalue Level Ceiling: local Conditions Weighted trivial coords
-- statement:
--   The Eigenvalue Level Ceiling construction uses the local Conditions Weighted trivial coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L613-L640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L613-L640

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem Formalism.EigenvalueLevelCeiling.localConditionsWeighted_trivial_coords (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (φ : (Fin 1 → K) →ₗ[K] K) (Mj : Submodule (𝓞 K) (Fin 1 → K)), Function.Injective φ ∧
      LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) ∧
      Mj.map (φ.restrictScalars (𝓞 K)) =
        (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
          ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
            ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) ∧
      (idx w Mj Mj : ℝ) ≤ 0 := by sorry
