-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_twistSetDouble_finset
-- name    : Formalism.EigenvalueLevelCeiling.twistSetDouble_finset
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:28:38.766155+00:00
-- url     : https://prove2.me/theorems/3b3ce15f-3201-4f02-bc4e-4aab4e8c6c50
-- title:
--   Eigenvalue Level Ceiling: twist Set Double finset
-- statement:
--   The Eigenvalue Level Ceiling construction uses the twist Set Double finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L505-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L505-L510

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
open Classical

theorem Formalism.EigenvalueLevelCeiling.twistSetDouble_finset (K : Type) [Field K] [NumberField K] [StarRing K] (J : Type) [Fintype J]
    (ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ w ∈ S, ∑ j, (ε0 w j + (if conjPl w = w then 0 else ε0 (conjPl w) j)) ≤ 1 / (plc w : ℝ) ^ 2) :
    ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2 := by sorry
