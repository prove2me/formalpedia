-- Prove2me | Theorems.Thm_Formalism_REAL_ite_zero_eq_mul_ite
-- name    : Formalism.REAL.ite_zero_eq_mul_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:26.11598+00:00
-- url     : https://prove2.me/theorems/84a1c0ba-1ca9-4755-8427-e7154182cc77
-- title:
--   REAL: ite zero eq mul ite
-- statement:
--   The REAL construction uses the ite zero eq mul ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L14-L16

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.ite_zero_eq_mul_ite (P : Prop) [Decidable P] (x : ℂ) :
    (if P then x else 0) = x * (if P then 1 else 0) := by sorry
