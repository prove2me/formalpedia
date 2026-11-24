-- Prove2me | Theorems.Thm_Formalism_REAL_arr_operator_one_apply
-- name    : Formalism.REAL.arr_operator_one_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:51.91479+00:00
-- url     : https://prove2.me/theorems/a7d9adae-67ff-4c5a-b102-19a5b40df149
-- title:
--   REAL: arr operator one apply
-- statement:
--   The REAL construction uses the arr operator one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L31-L37

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.arr_operator_one_apply (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n 1)
    (a b : Fin n) :
    arrE E 1 c d F (fun _ => (a, b)) =
      ((if a = c then F (fun _ => (d, b)) else 0) - (if b = d then F (fun _ => (a, c)) else 0))
        + E c d (F (fun _ => (a, b))) := by sorry
