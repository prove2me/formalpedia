-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_mem_X_join
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.mem_X_join
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:21.063395+00:00
-- url     : https://prove2.me/theorems/40dd5cdd-39e0-47d2-83a6-f75704fab294
-- title:
--   Block Start Points: mem X join
-- statement:
--   The Block Start Points construction uses the mem X join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L42-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L42-L71

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.mem_X_join (T : Tower E) (h : Pt E) (s : ℕ) (t : E) (i : ℕ) :
    join h s t ∈ T.X i ↔
      level h + s = i ∧ h ∈ T.X (level h) ∧ 1 ≤ s ∧ t ∈ T.Sg (level h + 1) s := by sorry
