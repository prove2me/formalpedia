-- Prove2me | Theorems.Thm_Formalism_REAL_prod_ofFn_apply_eq_zero
-- name    : Formalism.REAL.prod_ofFn_apply_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:59.934995+00:00
-- url     : https://prove2.me/theorems/a660be31-aac4-4081-be48-5dba289f728e
-- title:
--   REAL: prod of Fn apply eq zero
-- statement:
--   The REAL construction uses the prod of Fn apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuantumDetHighestWeightHolds.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/QuantumDetHighestWeightHolds.lean#L51-L66

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

theorem Formalism.REAL.prod_ofFn_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V) (j : Fin m),
      F j v = 0 → (∀ k, j < k → F k v = c k • v) → (List.ofFn F).prod v = 0 := by sorry
