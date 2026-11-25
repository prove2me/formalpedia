-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_integrable_mul_conj
-- name    : Formalism.L2.S.Pv.SchurTens.integrable_mul_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:09:50.375412+00:00
-- url     : https://prove2.me/theorems/011cf639-b63c-54cc-b67c-5b2cedb16c9c
-- title:
--   Schur Tens: integrable mul conj
-- statement:
--   The Schur Tens construction uses the integrable mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean#L38-L48

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

theorem Formalism.L2.S.Pv.SchurTens.integrable_mul_conj {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by sorry
