-- Prove2me | Theorems.Thm_Formalism_E_fock_smul_left
-- name    : Formalism.E.fock_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:38.175173+00:00
-- url     : https://prove2.me/theorems/fbc3742c-2193-4402-8402-e9319df5ee19
-- title:
--   E: fock smul left
-- statement:
--   The E construction uses the fock smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockSesq.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockSesq.lean#L28-L32

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

theorem Formalism.E.fock_smul_left (c : R) (f g : MvPolynomial τ R) : fock (c • f) g = c * fock f g := by sorry
