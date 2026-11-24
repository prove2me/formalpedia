-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_le_sum
-- name    : Formalism.GM.GaussNormRoots.multiset_sum_le_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:01.758676+00:00
-- url     : https://prove2.me/theorems/2e5e9a7a-3c82-4712-ba71-7f1779cc53d8
-- title:
--   Gauss Norm Roots: multiset sum le sum
-- statement:
--   The Gauss Norm Roots construction uses the multiset sum le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L49-L55

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

theorem Formalism.GM.GaussNormRoots.multiset_sum_le_sum {α : Type} (m : Multiset α) (f g : α → ℝ) (hfg : ∀ x, f x ≤ g x) :
    (m.map f).sum ≤ (m.map g).sum := by sorry
