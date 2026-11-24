-- Prove2me | Theorems.Thm_Formalism_UG_P_gLoc_int_iff
-- name    : Formalism.UG.P.gLoc_int_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:32:09.560869+00:00
-- url     : https://prove2.me/theorems/539e834f-d047-46bc-9fad-cd269f8c197a
-- title:
--   P: g Loc int iff
-- statement:
--   The P construction uses the g Loc int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L96-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L96-L122

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
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
variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.gLoc_int_iff (e : A ≃+* L) (T : Subring A) (O : Subring L) (hT : ∀ x, x ∈ T ↔ e x ∈ O)
    (g : GL n A) :
    g ∈ (bc (n := n) T.subtype).range ↔ bc (e : A →+* L) g ∈ (bc (n := n) O.subtype).range := by sorry
