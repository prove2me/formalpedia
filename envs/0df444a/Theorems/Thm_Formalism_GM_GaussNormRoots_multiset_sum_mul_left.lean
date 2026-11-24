-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_mul_left
-- name    : Formalism.GM.GaussNormRoots.multiset_sum_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:03.21586+00:00
-- url     : https://prove2.me/theorems/be1d5f12-f869-4129-868a-d90cdf312f1a
-- title:
--   Gauss Norm Roots: multiset sum mul left
-- statement:
--   The Gauss Norm Roots construction uses the multiset sum mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L72-L77

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

theorem Formalism.GM.GaussNormRoots.multiset_sum_mul_left {α : Type} (m : Multiset α) (c : ℝ) (f : α → ℝ) :
    (m.map fun x => c * f x).sum = c * (m.map f).sum := by sorry
