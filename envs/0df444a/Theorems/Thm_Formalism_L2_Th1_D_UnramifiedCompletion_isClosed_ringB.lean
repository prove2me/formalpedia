-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_isClosed_ringB
-- name    : Formalism.L2.Th1.D.UnramifiedCompletion.isClosed_ringB
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:40.230191+00:00
-- url     : https://prove2.me/theorems/c6491b9c-e65b-48e5-b420-b749e2cfe551
-- title:
--   Unramified Completion: is Closed ring B
-- statement:
--   The Unramified Completion construction uses the is Closed ring B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L122-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L122-L122

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
open UnramifiedCompletion
open Formalism.L2.Th1.D.UnramifiedCompletion
variable {l : ℕ} [hl : Fact l.Prime]

theorem Formalism.L2.Th1.D.UnramifiedCompletion.isClosed_ringB : IsClosed (ringB l : Set ℂ_[l]) := by sorry
