-- Prove2me | Theorems.Thm_Formalism_E_fock_smul_right
-- name    : Formalism.E.fock_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:18.362911+00:00
-- url     : https://prove2.me/theorems/a2139707-05fe-43d2-a7a1-ae2cef70a0bc
-- title:
--   E: fock smul right
-- statement:
--   The E construction uses the fock smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockSesq.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockSesq.lean#L39-L45

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

theorem Formalism.E.fock_smul_right (c : R) (f g : MvPolynomial τ R) :
    fock f (c • g) = star c * fock f g := by sorry
