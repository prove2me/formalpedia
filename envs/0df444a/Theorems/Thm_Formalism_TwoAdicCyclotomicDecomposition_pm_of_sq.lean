-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_pm_of_sq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.pm_of_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:55.533809+00:00
-- url     : https://prove2.me/theorems/9c7aa237-a77d-4e4b-b7d8-9e48a1a6b6d9
-- title:
--   Two Adic Cyclotomic Decomposition: pm of sq
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the pm of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L68-L71

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

theorem Formalism.TwoAdicCyclotomicDecomposition.pm_of_sq {x : L} {c : ℕ} (hx : x ^ 2 = -(c : L)) (σ : Gal(L/ℚ)) :
    σ x = x ∨ σ x = -x := by sorry
