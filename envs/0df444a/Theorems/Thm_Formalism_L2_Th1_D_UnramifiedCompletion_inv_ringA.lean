-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_inv_ringA
-- name    : Formalism.L2.Th1.D.UnramifiedCompletion.inv_ringA
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:41.116943+00:00
-- url     : https://prove2.me/theorems/7c57c748-0fc0-449d-b39e-b0817e057cba
-- title:
--   Unramified Completion: inv ring A
-- statement:
--   The Unramified Completion construction uses the inv ring A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L175-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L175-L194

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

theorem Formalism.L2.Th1.D.UnramifiedCompletion.inv_ringA (hA : PerA l) {u : ℂ_[l]} (hu : u ∈ ringA l) (h : ‖u‖ = 1) : u⁻¹ ∈ ringB l := by sorry
