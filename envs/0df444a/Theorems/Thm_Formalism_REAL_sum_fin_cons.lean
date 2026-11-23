-- Prove2me | Theorems.Thm_Formalism_REAL_sum_fin_cons
-- name    : Formalism.REAL.sum_fin_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:54.77418+00:00
-- url     : https://prove2.me/theorems/dbd9add8-f2fe-4161-bb7f-333f41f527b6
-- title:
--   REAL: sum fin cons
-- statement:
--   The REAL construction uses the sum fin cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L296-L301

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.sum_fin_cons {X M : Type*} [Fintype X] [AddCommMonoid M] (f : (Fin (j+1) → X) → M) :
    ∑ α, f α = ∑ α' : Fin j → X, ∑ β : Fin 1 → X, f (Fin.cons (β 0) α') := by sorry
