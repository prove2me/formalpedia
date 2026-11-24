-- Prove2me | Theorems.Thm_Formalism_Q3_CMRootsOfUnity_no_prime_root
-- name    : Formalism.Q3.CMRootsOfUnity.no_prime_root
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:04.385687+00:00
-- url     : https://prove2.me/theorems/96852727-457b-4a05-9d4d-362bc0a8681d
-- title:
--   CMRoots Of Unity: no prime root
-- statement:
--   The CMRoots Of Unity construction uses the no prime root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L76-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L76-L97

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

theorem Formalism.Q3.CMRootsOfUnity.no_prime_root (hH : HostGalois) (hq : Hyp3 q) (hα : IsHost q α) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (η : E) (hη : IsPrimitiveRoot η p) : False := by sorry
