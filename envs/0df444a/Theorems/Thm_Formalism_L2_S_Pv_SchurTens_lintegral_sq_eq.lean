-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_lintegral_sq_eq
-- name    : Formalism.L2.S.Pv.SchurTens.lintegral_sq_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:58.371394+00:00
-- url     : https://prove2.me/theorems/7006452f-9af5-57ad-b356-3168bb81227d
-- title:
--   Schur Tens: lintegral sq eq
-- statement:
--   The Schur Tens construction uses the lintegral sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean#L28-L34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem Formalism.L2.S.Pv.SchurTens.lintegral_sq_eq {u : X → ℂ} (hu : MemLp u 2 μ) :
    ∫ x, ‖u x‖ ^ 2 ∂μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by sorry
