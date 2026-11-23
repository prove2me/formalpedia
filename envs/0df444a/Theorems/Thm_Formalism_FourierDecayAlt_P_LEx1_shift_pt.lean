-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_shift_pt
-- name    : Formalism.FourierDecayAlt.P.LEx1.shift_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:52.998234+00:00
-- url     : https://prove2.me/theorems/9ed750d7-5dc0-4a1a-8b47-136e6f22aebb
-- title:
--   LEx1: shift pt
-- statement:
--   The LEx1 construction uses the shift pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StepClaimFromStepsFull.lean#L276-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StepClaimFromStepsFull.lean#L276-L328

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

theorem Formalism.FourierDecayAlt.P.LEx1.shift_pt {B : Base} (S : Step B) (CR Cd : ℝ) (hCR : 0 ≤ CR) (hCd : 0 ≤ Cd) (hW : S.WPos) (h5 : S.ShiftFormula)
    (hRes : S.Residues CR) (hWR : S.WeightRatio Cd) (Y s : ℝ) (hY : Y ∈ S.J) (hYs : Y + s ∈ S.J) (ω : B.Ω) :
    LE.sq B (S.d Y) (S.gs Y s) ω ≤ (1 + CR) ^ 2 * (Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) := by sorry
