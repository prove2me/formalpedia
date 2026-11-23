-- Prove2me | Theorems.Thm_Formalism_REAL_sum_update_first_index_swap
-- name    : Formalism.REAL.sum_update_first_index_swap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:17.600669+00:00
-- url     : https://prove2.me/theorems/289c65ec-6639-44c7-be35-3c0fab248149
-- title:
--   REAL: sum update first index swap
-- statement:
--   The REAL construction uses the sum update first index swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L268-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L268-L286

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

theorem Formalism.REAL.sum_update_first_index_swap {M : Type*} [AddCommMonoid M] {j : ℕ} (i : Fin j) (c d : Fin n)
    (f : (Fin j → Fin n × Fin n) → (Fin j → Fin n × Fin n) → M) :
    ∑ α, (if (α i).1 = c then f α (Function.update α i (d, (α i).2)) else 0) =
      ∑ β, (if (β i).1 = d then f (Function.update β i (c, (β i).2)) β else 0) := by sorry
