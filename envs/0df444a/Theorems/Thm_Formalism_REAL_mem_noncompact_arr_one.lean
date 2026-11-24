-- Prove2me | Theorems.Thm_Formalism_REAL_mem_noncompact_arr_one
-- name    : Formalism.REAL.mem_noncompact_arr_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:40.576966+00:00
-- url     : https://prove2.me/theorems/aa986a96-72da-4116-a1b1-c41cbfe7e84a
-- title:
--   REAL: mem noncompact arr one
-- statement:
--   The REAL construction uses the mem noncompact arr one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L55-L63

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

theorem Formalism.REAL.mem_noncompact_arr_one {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n 1}
    (h1 : ∀ a b, ε a ≠ ε b → F (fun _ => (a, b)) ∈ kSpan ε E u)
    (h2 : ∀ a b, ε a = ε b → F (fun _ => (a, b)) = 0) : F ∈ arrV0 ε E u 1 := by sorry
