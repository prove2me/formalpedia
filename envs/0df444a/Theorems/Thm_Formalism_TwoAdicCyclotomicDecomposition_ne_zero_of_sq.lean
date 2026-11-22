-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ne_zero_of_sq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ne_zero_of_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:57.62747+00:00
-- url     : https://prove2.me/theorems/1cf6bcc4-2e7a-4d8a-9b41-8a8c73c53853
-- title:
--   Two Adic Cyclotomic Decomposition: ne zero of sq
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the ne zero of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L73-L78

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.TwoAdicCyclotomicDecomposition.ne_zero_of_sq {x : L} {c : ℕ} (hc : c ≠ 0) (hx : x ^ 2 = -(c : L)) : x ≠ 0 := by sorry
