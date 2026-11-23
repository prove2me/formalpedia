-- Prove2me | Theorems.Thm_Formalism_REAL_sum_update_second_index_swap
-- name    : Formalism.REAL.sum_update_second_index_swap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:08.68958+00:00
-- url     : https://prove2.me/theorems/c9743921-105b-4e08-bbad-f4d1bffe3587
-- title:
--   REAL: sum update second index swap
-- statement:
--   The REAL construction uses the sum update second index swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L288-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L288-L306

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

theorem Formalism.REAL.sum_update_second_index_swap {M : Type*} [AddCommMonoid M] {j : ℕ} (i : Fin j) (c d : Fin n)
    (f : (Fin j → Fin n × Fin n) → (Fin j → Fin n × Fin n) → M) :
    ∑ α, (if (α i).2 = d then f α (Function.update α i ((α i).1, c)) else 0) =
      ∑ β, (if (β i).2 = c then f (Function.update β i ((β i).1, d)) β else 0) := by sorry
