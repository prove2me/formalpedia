-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_eval_idPoint_lpMinor
-- name    : Formalism.GradedWeylDivisibility.eval_idPoint_lpMinor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:34.075541+00:00
-- url     : https://prove2.me/theorems/eb78d4ee-02c6-4d12-bc86-b4e4a82100a0
-- title:
--   Graded Weyl Divisibility: eval id Point lp Minor
-- statement:
--   The Graded Weyl Divisibility construction uses the eval id Point lp Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwrowLemmas.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwrowLemmas.lean#L10-L17

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial

theorem Formalism.GradedWeylDivisibility.eval_idPoint_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r)
    (hn : s ≤ n) : eval (idPoint R r n) (lpMinor R s hr hn) = 1 := by sorry
