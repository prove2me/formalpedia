-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_isSchur_of_dense
-- name    : Formalism.L2.S.Pv.SchurTens.isSchur_of_dense
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:45.65725+00:00
-- url     : https://prove2.me/theorems/f15a50c6-39f1-4c6d-9872-aaa2877d5b94
-- title:
--   Schur Tens: is Schur of dense
-- statement:
--   The Schur Tens construction uses the is Schur of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L184-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L184-L215

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

theorem Formalism.L2.S.Pv.SchurTens.isSchur_of_dense (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (hSp : ∀ a ∈ Sp, ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, SP m σs D a b a' b') :
    IsSchur m σs D := by sorry
