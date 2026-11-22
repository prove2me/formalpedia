-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_mem_Id
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_mem_Id
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:48.448976+00:00
-- url     : https://prove2.me/theorems/4aad5478-7729-4330-9380-3764c24da144
-- title:
--   Two Adic Cyclotomic Decomposition: odd mem Id
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd mem Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L285-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L285-L295

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_mem_Id (n : ℕ) (g : GalL n) : g ∈ Id n ↔ g = 1 ∨ g = (1, 1, -1) := by sorry
