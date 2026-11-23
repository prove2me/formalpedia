-- Prove2me | Theorems.Thm_Formalism_E_fock_add_left
-- name    : Formalism.E.fock_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:27.539252+00:00
-- url     : https://prove2.me/theorems/ddc6ba62-6fe1-4bbf-b4e2-78f51e74b61e
-- title:
--   E: fock add left
-- statement:
--   The E construction uses the fock add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockSesq.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockSesq.lean#L20-L26

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open Formalism Formalism.E
variable {R τ : Type*} [CommRing R] [StarRing R]

theorem Formalism.E.fock_add_left (f f' g : MvPolynomial τ R) : fock (f + f') g = fock f g + fock f' g := by sorry
