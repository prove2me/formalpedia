-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_prod_pos
-- name    : Formalism.GM.GaussNormRoots.multiset_prod_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:37.697805+00:00
-- url     : https://prove2.me/theorems/76693dfd-c384-4bd4-bcb8-2e74093910b1
-- title:
--   Gauss Norm Roots: multiset prod pos
-- statement:
--   The Gauss Norm Roots construction uses the multiset prod pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L95-L101

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

theorem Formalism.GM.GaussNormRoots.multiset_prod_pos {α : Type} (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    0 < (m.map f).prod := by sorry
