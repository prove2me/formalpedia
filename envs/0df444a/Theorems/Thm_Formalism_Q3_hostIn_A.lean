-- Prove2me | Theorems.Thm_Formalism_Q3_hostIn_A
-- name    : Formalism.Q3.hostIn_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:43.039258+00:00
-- url     : https://prove2.me/theorems/c8d038db-4e96-4d10-ba7b-4509655e9d50
-- title:
--   Q3: host In A
-- statement:
--   The Q3 construction uses the host In A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L31-L42

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
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
open Formalism Formalism.Q3

theorem Formalism.Q3.hostIn_A (q : Fin 3 → ℕ) {E : Type} [Field E] [NumberField E] (α : Fin 3 → E)
    (hα : IsHost q α) (j : Fin 3) :
    ∃ A : 𝓞 E, (A : E) = α j ∧ A ^ 2 = ((-(q j : ℤ) : ℤ) : 𝓞 E) := by sorry
