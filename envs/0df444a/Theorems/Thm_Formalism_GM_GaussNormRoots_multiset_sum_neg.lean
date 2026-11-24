-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_neg
-- name    : Formalism.GM.GaussNormRoots.multiset_sum_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:49.545985+00:00
-- url     : https://prove2.me/theorems/4448f1e6-7cc3-44ca-869b-fcc46588cbad
-- title:
--   Gauss Norm Roots: multiset sum neg
-- statement:
--   The Gauss Norm Roots construction uses the multiset sum neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L57-L62

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots

theorem Formalism.GM.GaussNormRoots.multiset_sum_neg {α : Type} (m : Multiset α) (f : α → ℝ) :
    (m.map fun x => -f x).sum = -(m.map f).sum := by sorry
