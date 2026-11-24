-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_mem_of_pow_mul
-- name    : Formalism.L2.Th1.D.UnramifiedCompletion.mem_of_pow_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:26.596417+00:00
-- url     : https://prove2.me/theorems/2f4c99e3-6a11-48d1-b429-1fc0f19abf3d
-- title:
--   Unramified Completion: mem of pow mul
-- statement:
--   The Unramified Completion construction uses the mem of pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L247-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean#L247-L263

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

theorem Formalism.L2.Th1.D.UnramifiedCompletion.mem_of_pow_mul (hdiv : DivB l) : ∀ (k : ℕ) (x : ℂ_[l]), ‖x‖ ≤ 1 →
    (l : ℂ_[l]) ^ k * x ∈ ringB l → x ∈ ringB l := by sorry
