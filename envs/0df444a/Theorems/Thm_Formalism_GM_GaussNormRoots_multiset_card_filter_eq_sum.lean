-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_card_filter_eq_sum
-- name    : Formalism.GM.GaussNormRoots.multiset_card_filter_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:54.964713+00:00
-- url     : https://prove2.me/theorems/79694d1f-de14-4d84-9777-c8399c2684bc
-- title:
--   Gauss Norm Roots: multiset card filter eq sum
-- statement:
--   The Gauss Norm Roots construction uses the multiset card filter eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L79-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L79-L93

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

theorem Formalism.GM.GaussNormRoots.multiset_card_filter_eq_sum {α : Type} (m : Multiset α) (P : α → Prop) [DecidablePred P] :
    ((m.filter P).card : ℝ) = (m.map fun x => if P x then (1 : ℝ) else 0).sum := by sorry
