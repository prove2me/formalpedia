-- Prove2me | Theorems.Thm_Formalism_Q3_CMRootsOfUnity_no_three
-- name    : Formalism.Q3.CMRootsOfUnity.no_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:02.178812+00:00
-- url     : https://prove2.me/theorems/c2757eb8-6852-4dbe-bb1f-cf8b7d8514cf
-- title:
--   CMRoots Of Unity: no three
-- statement:
--   The CMRoots Of Unity construction uses the no three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L107-L121

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
variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

theorem Formalism.Q3.CMRootsOfUnity.no_three (hK : MQKummer) (hq : Hyp3 q) (hq3 : ∀ i, q i ≠ 3) (hα : IsHost q α) (ω : E)
    (hω : IsPrimitiveRoot ω 3) : False := by sorry
