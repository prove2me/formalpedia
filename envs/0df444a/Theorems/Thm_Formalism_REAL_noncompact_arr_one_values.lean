-- Prove2me | Theorems.Thm_Formalism_REAL_noncompact_arr_one_values
-- name    : Formalism.REAL.noncompact_arr_one_values
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:04:03.52471+00:00
-- url     : https://prove2.me/theorems/cad9eca0-f2e1-44e6-becd-a2ac4b48a60e
-- title:
--   REAL: noncompact arr one values
-- statement:
--   The REAL construction uses the noncompact arr one values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L44-L53

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

theorem Formalism.REAL.noncompact_arr_one_values {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n 1}
    (hF : F ∈ arrV0 ε E u 1) (a b : Fin n) :
    (ε a ≠ ε b → F (fun _ => (a, b)) ∈ kSpan ε E u) ∧ (ε a = ε b → F (fun _ => (a, b)) = 0) := by sorry
