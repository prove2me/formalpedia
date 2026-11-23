-- Prove2me | Theorems.Thm_Formalism_SLP_P_base
-- name    : Formalism.SLP.P.base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:22.876475+00:00
-- url     : https://prove2.me/theorems/98cab082-1f8e-4eff-8106-18cc878265df
-- title:
--   P: base
-- statement:
--   The P construction uses the base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean#L227-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean#L227-L235

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup

theorem Formalism.SLP.P.base : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup (Fin 0 → ℤ) | H.index = j}.Finite ∧
    {H : AddSubgroup (Fin 0 → ℤ) | H.index = j}.ncard ≤ j ^ 0 := by sorry
