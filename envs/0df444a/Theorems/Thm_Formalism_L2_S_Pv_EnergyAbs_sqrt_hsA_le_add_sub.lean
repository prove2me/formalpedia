-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_sqrt_hsA_le_add_sub
-- name    : Formalism.L2.S.Pv.EnergyAbs.sqrt_hsA_le_add_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:38.988687+00:00
-- url     : https://prove2.me/theorems/3270f421-43e3-5318-938b-0f96d7abe01a
-- title:
--   Energy Abs: sqrt hs A le add sub
-- statement:
--   The Energy Abs construction uses the sqrt hs A le add sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean#L89-L95

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem Formalism.L2.S.Pv.EnergyAbs.sqrt_hsA_le_add_sub (A B : V' →L[ℂ] V) :
    Real.sqrt (hsA A) ≤ Real.sqrt (hsA B) + Real.sqrt (hsA (A - B)) := by sorry
