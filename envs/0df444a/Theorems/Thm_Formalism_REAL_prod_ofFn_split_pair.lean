-- Prove2me | Theorems.Thm_Formalism_REAL_prod_ofFn_split_pair
-- name    : Formalism.REAL.prod_ofFn_split_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:40.405445+00:00
-- url     : https://prove2.me/theorems/ab6f9f4e-a0c4-4370-abde-c0e8065baf15
-- title:
--   REAL: prod of Fn split pair
-- statement:
--   The REAL construction uses the prod of Fn split pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L71-L79

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
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

theorem Formalism.REAL.prod_ofFn_split_pair {M : Type*} [Monoid M] {t : ℕ} (f : Fin t → M) (i : ℕ) (hi : i + 1 < t) :
    (List.ofFn f).prod = ((List.ofFn f).take i).prod * (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by sorry
