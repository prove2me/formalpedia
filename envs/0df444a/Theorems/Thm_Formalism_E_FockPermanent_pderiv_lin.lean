-- Prove2me | Theorems.Thm_Formalism_E_FockPermanent_pderiv_lin
-- name    : Formalism.E.FockPermanent.pderiv_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:01.642828+00:00
-- url     : https://prove2.me/theorems/ef561767-cb77-4abc-b849-e90b401265ac
-- title:
--   Fock Permanent: pderiv lin
-- statement:
--   The Fock Permanent construction uses the pderiv lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L68-L78

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

theorem Formalism.E.FockPermanent.pderiv_lin (z : MvPolynomial τ R) (hz : z.IsHomogeneous 1) (k : τ) :
    pderiv k z = C (z.coeff (Finsupp.single k 1)) := by sorry
