-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_smul_b
-- name    : Formalism.L2.S.Pv.SchurTens.SP_smul_b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:12.585874+00:00
-- url     : https://prove2.me/theorems/84c7cc4d-dcb6-488b-bf5c-2921ce1e7a3e
-- title:
--   Schur Tens: SP smul b
-- statement:
--   The Schur Tens construction uses the SP smul b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L84-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L84-L94

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

theorem Formalism.L2.S.Pv.SchurTens.SP_smul_b (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a (c • b) a' b' := by sorry
