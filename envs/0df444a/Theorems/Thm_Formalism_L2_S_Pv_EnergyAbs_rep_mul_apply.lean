-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_rep_mul_apply
-- name    : Formalism.L2.S.Pv.EnergyAbs.rep_mul_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:07:30.125942+00:00
-- url     : https://prove2.me/theorems/8707c609-f44d-57f8-864b-cb262dfe313c
-- title:
--   Energy Abs: rep mul apply
-- statement:
--   The Energy Abs construction uses the rep mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean#L104-L107

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
variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]

theorem Formalism.L2.S.Pv.EnergyAbs.rep_mul_apply {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ x (σ y a) = σ (x * y) a := by sorry
