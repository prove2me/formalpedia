-- Prove2me | Theorems.Thm_Formalism_E_FockPermanent_bil_add_left
-- name    : Formalism.E.FockPermanent.bil_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:21.948986+00:00
-- url     : https://prove2.me/theorems/6816bbd6-be7a-4083-a0e2-464747e2d765
-- title:
--   Fock Permanent: bil add left
-- statement:
--   The Fock Permanent construction uses the bil add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L21-L27

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

theorem Formalism.E.FockPermanent.bil_add_left (f f' g : MvPolynomial τ R) : bil (f + f') g = bil f g + bil f' g := by sorry
