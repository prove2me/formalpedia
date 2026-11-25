-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_localConditionsWeighted_trivial_instance
-- name    : Formalism.EigenvalueLevelCeiling.localConditionsWeighted_trivial_instance
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:47.186685+00:00
-- url     : https://prove2.me/theorems/4a367589-c162-5324-921e-31c49a9af3c4
-- title:
--   Eigenvalue Level Ceiling: local Conditions Weighted trivial instance
-- statement:
--   The Eigenvalue Level Ceiling construction uses the local Conditions Weighted trivial instance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L576-L611
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L576-L611

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

theorem Formalism.EigenvalueLevelCeiling.localConditionsWeighted_trivial_instance (w : HeightOneSpectrum (𝓞 K)) :
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] K), Function.Injective φ →
    LinearMap.range φ = eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) =
      cut (eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) ⊓ ⊤) (unitLat K) →
    Tj.map (φ.restrictScalars (𝓞 K)) =
      (((unitLat K).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map
        ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K))).map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) →
      (idx w Mj Tj : ℝ) ≤
        (((0 : ℕ) : ℝ) - (vw w (1 : K) : ℝ) + (vw w ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) : ℝ)) * (d : ℝ) +
          (0 + (finrank K K : ℝ) * (vw w ((Nat.card (⊤ : Subgroup Unit) : ℕ) : K) : ℝ)) /
            ((⊤ : Subgroup Unit).index : ℝ) + 0 := by sorry
