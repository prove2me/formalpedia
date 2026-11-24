-- Prove2me | Theorems.Thm_Formalism_UG_P_levelvsplit_coe_bc
-- name    : Formalism.UG.P.levelvsplit_coe_bc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:17.79989+00:00
-- url     : https://prove2.me/theorems/db61e874-728c-444d-8d6c-edbde223ea7e
-- title:
--   P: levelvsplit coe bc
-- statement:
--   The P construction uses the levelvsplit coe bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L14-L16

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
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
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelvsplit_coe_bc (f : R →+* A) (u : GL n R) :
    ((bc (n := n) f u : GL n A) : Matrix n n A) = (u : Matrix n n R).map f := by sorry
