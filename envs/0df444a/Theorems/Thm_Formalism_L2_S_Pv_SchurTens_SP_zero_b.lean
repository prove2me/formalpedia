-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_zero_b
-- name    : Formalism.L2.S.Pv.SchurTens.SP_zero_b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:21.831469+00:00
-- url     : https://prove2.me/theorems/22e4c8b3-cebd-4244-8b6b-a80702ee44bd
-- title:
--   Schur Tens: SP zero b
-- statement:
--   The Schur Tens construction uses the SP zero b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L68-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
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
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

theorem Formalism.L2.S.Pv.SchurTens.SP_zero_b (a a' b' : Hs) : SP m σs D a 0 a' b' := by sorry
