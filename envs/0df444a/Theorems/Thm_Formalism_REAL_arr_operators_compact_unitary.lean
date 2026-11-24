-- Prove2me | Theorems.Thm_Formalism_REAL_arr_operators_compact_unitary
-- name    : Formalism.REAL.arr_operators_compact_unitary
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:14.935736+00:00
-- url     : https://prove2.me/theorems/a5584f2c-b150-4074-982c-c122da0fc1e7
-- title:
--   REAL: arr operators compact unitary
-- statement:
--   The REAL construction uses the arr operators compact unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L427-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L427-L443

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
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

theorem Formalism.REAL.arr_operators_compact_unitary {j : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hU : IsUnitary ε E) : KUnit ε (arrE E j) := by sorry
