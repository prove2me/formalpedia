-- Prove2me | Theorems.Thm_Formalism_UG_P_sf_gram
-- name    : Formalism.UG.P.sf_gram
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:34:12.425328+00:00
-- url     : https://prove2.me/theorems/a19245bc-3a97-449f-9052-1b1e24a7390f
-- title:
--   P: sf gram
-- statement:
--   The P construction uses the sf gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L77-L81

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.sf_gram {A : Type} [CommRing A] (σ : A →+* A) (J M : Matrix n n A) (a b : n) :
    (cT σ M * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by sorry
