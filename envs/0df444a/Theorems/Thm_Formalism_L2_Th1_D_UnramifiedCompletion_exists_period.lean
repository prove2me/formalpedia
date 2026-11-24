-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_exists_period
-- name    : Formalism.L2.Th1.D.UnramifiedCompletion.exists_period
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:47.655189+00:00
-- url     : https://prove2.me/theorems/a09b5d7f-e939-4695-8fa8-dd97b3062982
-- title:
--   Unramified Completion: exists period
-- statement:
--   The Unramified Completion construction uses the exists period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L48-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L48-L98

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.L2.Th1.D.UnramifiedCompletion
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}

theorem Formalism.L2.Th1.D.UnramifiedCompletion.exists_period {x : ℂ_[l]} (hx : x ∈ ringA l) :
    ∃ f : ℕ, 0 < f ∧
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) ⟨x, hx⟩) ^ (l ^ f)
        = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) ⟨x, hx⟩ := by sorry
