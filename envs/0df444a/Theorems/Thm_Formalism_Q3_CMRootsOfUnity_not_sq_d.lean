-- Prove2me | Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_sq_d
-- name    : Formalism.Q3.CMRootsOfUnity.not_sq_d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:18.951943+00:00
-- url     : https://prove2.me/theorems/1aca0b9d-6ef8-4f0e-b6e3-73df2ceb2ab2
-- title:
--   CMRoots Of Unity: not sq d
-- statement:
--   The CMRoots Of Unity construction uses the not sq d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L14-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L14-L45

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}

theorem Formalism.Q3.CMRootsOfUnity.not_sq_d (hq : Hyp3 q) (d : ℤ) (S : Finset (Fin 3)) (hS : S.Nonempty ∨ d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) :
    ¬ IsSquare ((d : ℚ) * ∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by sorry
