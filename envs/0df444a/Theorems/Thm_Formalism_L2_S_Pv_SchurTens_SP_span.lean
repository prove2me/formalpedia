-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_span
-- name    : Formalism.L2.S.Pv.SchurTens.SP_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:58.814722+00:00
-- url     : https://prove2.me/theorems/b3cf9434-a381-42d3-8d49-ce061372d9b3
-- title:
--   Schur Tens: SP span
-- statement:
--   The Schur Tens construction uses the SP span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L108-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensSpan.lean#L108-L143

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

theorem Formalism.L2.S.Pv.SchurTens.SP_span {E : Set Hs} (h : ∀ a ∈ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') :
    ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ Submodule.span ℂ E,
      ∀ b' ∈ Submodule.span ℂ E, SP m σs D a b a' b' := by sorry
