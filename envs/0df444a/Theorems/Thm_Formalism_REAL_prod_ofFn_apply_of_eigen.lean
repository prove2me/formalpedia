-- Prove2me | Theorems.Thm_Formalism_REAL_prod_ofFn_apply_of_eigen
-- name    : Formalism.REAL.prod_ofFn_apply_of_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:49.577739+00:00
-- url     : https://prove2.me/theorems/5509749a-4bb1-4b5c-aaee-34916630d35e
-- title:
--   REAL: prod of Fn apply of eigen
-- statement:
--   The REAL construction uses the prod of Fn apply of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuantumDetHighestWeightHolds.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuantumDetHighestWeightHolds.lean#L39-L49

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
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

theorem Formalism.REAL.prod_ofFn_apply_of_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V),
      (∀ k, F k v = c k • v) → (List.ofFn F).prod v = (∏ k, c k) • v := by sorry
