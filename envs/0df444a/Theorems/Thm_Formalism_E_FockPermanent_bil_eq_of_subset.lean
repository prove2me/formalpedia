-- Prove2me | Theorems.Thm_Formalism_E_FockPermanent_bil_eq_of_subset
-- name    : Formalism.E.FockPermanent.bil_eq_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:22.038493+00:00
-- url     : https://prove2.me/theorems/f8ccfe84-bde2-4464-957b-64cc41f1726f
-- title:
--   Fock Permanent: bil eq of subset
-- statement:
--   The Fock Permanent construction uses the bil eq of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean#L15-L19

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

theorem Formalism.E.FockPermanent.bil_eq_of_subset {f g : MvPolynomial τ R} {S : Finset (τ →₀ ℕ)} (h : f.support ⊆ S) :
    bil f g = ∑ m ∈ S, f.coeff m * g.coeff m * (Formalism.A.mfact m : R) := by sorry
