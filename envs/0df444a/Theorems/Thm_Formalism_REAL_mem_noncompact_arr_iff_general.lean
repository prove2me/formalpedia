-- Prove2me | Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff_general
-- name    : Formalism.REAL.mem_noncompact_arr_iff_general
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:29.208775+00:00
-- url     : https://prove2.me/theorems/e98c5e3a-9200-4375-823b-548fbe0e8b6b
-- title:
--   REAL: mem noncompact arr iff general
-- statement:
--   The REAL construction uses the mem noncompact arr iff general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L39-L42

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

theorem Formalism.REAL.mem_noncompact_arr_iff_general {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : ℕ}
    (F : Arr V n j) :
    F ∈ arrV0 ε E u j ↔ ∀ α, F α ∈ (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥) := by sorry
