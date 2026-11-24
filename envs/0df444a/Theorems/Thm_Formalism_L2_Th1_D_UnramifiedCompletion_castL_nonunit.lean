-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_castL_nonunit
-- name    : Formalism.L2.Th1.D.UnramifiedCompletion.castL_nonunit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:12:05.721625+00:00
-- url     : https://prove2.me/theorems/b1f910cf-53f0-42e7-9838-4e1ea6948fac
-- title:
--   Unramified Completion: cast L nonunit
-- statement:
--   The Unramified Completion construction uses the cast L nonunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L37-L46

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

theorem Formalism.L2.Th1.D.UnramifiedCompletion.castL_nonunit : ((l : ℕ) : ringA l) ∈ nonunits (ringA l) := by sorry
