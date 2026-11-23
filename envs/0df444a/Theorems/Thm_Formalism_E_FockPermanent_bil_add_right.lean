-- Prove2me | Theorems.Thm_Formalism_E_FockPermanent_bil_add_right
-- name    : Formalism.E.FockPermanent.bil_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:33.097048+00:00
-- url     : https://prove2.me/theorems/a391a40e-d4db-4c1e-8623-66f5e4918fba
-- title:
--   Fock Permanent: bil add right
-- statement:
--   The Fock Permanent construction uses the bil add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L29-L32

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
open Formalism Formalism.E
open Formalism.E.FockPermanent
variable {R τ : Type*} [CommRing R]

theorem Formalism.E.FockPermanent.bil_add_right (f g g' : MvPolynomial τ R) : bil f (g + g') = bil f g + bil f g' := by sorry
