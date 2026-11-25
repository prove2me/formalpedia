-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_coeff_sub_b
-- name    : Formalism.L2.S.Pv.SchurTens.coeff_sub_b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:09.821488+00:00
-- url     : https://prove2.me/theorems/be6691dc-23f1-44b3-9cbe-18995af8d980
-- title:
--   Schur Tens: coeff sub b
-- statement:
--   The Schur Tens construction uses the coeff sub b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L73-L75

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

theorem Formalism.L2.S.Pv.SchurTens.coeff_sub_b (a b₁ b₂ : Hs) : (fun x => coeff σs a b₁ x - coeff σs a b₂ x) = coeff σs a (b₁ - b₂) := by sorry
