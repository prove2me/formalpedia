-- Prove2me | Theorems.Thm_Formalism_SLP_P_step
-- name    : Formalism.SLP.P.step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:25.414218+00:00
-- url     : https://prove2.me/theorems/88c84fb3-8c42-4dbf-b638-3ea7835cdcbd
-- title:
--   P: step
-- statement:
--   The P construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean#L58-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean#L58-L172

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

theorem Formalism.SLP.P.step {A : Type*} [AddCommGroup A] (n : ℕ)
    (hgen : ∀ K : AddSubgroup A, ∃ v : Fin n → A, AddSubgroup.closure (Set.range v) = K)
    (ih : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup A | H.index = j}.Finite ∧
      {H : AddSubgroup A | H.index = j}.ncard ≤ j ^ n) :
    ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup (ℤ × A) | H.index = j}.Finite ∧
      {H : AddSubgroup (ℤ × A) | H.index = j}.ncard ≤ j ^ (n + 1) := by sorry
