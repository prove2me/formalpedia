-- Prove2me | Theorems.Thm_Formalism_GM_GaussNormRoots_logb_multiset_prod
-- name    : Formalism.GM.GaussNormRoots.logb_multiset_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:12.766272+00:00
-- url     : https://prove2.me/theorems/f10c0ab6-6625-411f-8b91-1d849b40f3c6
-- title:
--   Gauss Norm Roots: logb multiset prod
-- statement:
--   The Gauss Norm Roots construction uses the logb multiset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieRoots.lean#L103-L109

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

theorem Formalism.GM.GaussNormRoots.logb_multiset_prod {α : Type} (b : ℝ) (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    Real.logb b (m.map f).prod = (m.map fun x => Real.logb b (f x)).sum := by sorry
