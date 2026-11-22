-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_mem_Iq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_mem_Iq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:54.892948+00:00
-- url     : https://prove2.me/theorems/128c7c3d-5b27-4da3-b122-eae6e03dcf72
-- title:
--   Two Adic Cyclotomic Decomposition: odd mem Iq
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd mem Iq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L273-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L273-L283

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

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_mem_Iq (n : ℕ) (g : GalL n) : g ∈ Iq n ↔ g = 1 ∨ g = (1, -1, 1) := by sorry
