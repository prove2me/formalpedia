-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_mem_stdLat
-- name    : Formalism.UG.P.afsplit_mem_stdLat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:35.701801+00:00
-- url     : https://prove2.me/theorems/60c715c1-fbf4-44a0-9967-29ecc56b7830
-- title:
--   P: afsplit mem std Lat
-- statement:
--   The P construction uses the afsplit mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L14-L22

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.afsplit_mem_stdLat (S : Subring A) (x : n → A) :
    x ∈ stdLat (n := n) (A := A) S ↔ ∀ i, x i ∈ S := by sorry
