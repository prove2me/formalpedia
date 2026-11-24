-- Prove2me | Theorems.Thm_Formalism_UG_polyRep_apply
-- name    : Formalism.UG.polyRep_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:46.917513+00:00
-- url     : https://prove2.me/theorems/d49fb8a4-e3e7-411a-b571-853b6d25d75c
-- title:
--   UG: poly Rep apply
-- statement:
--   The UG construction uses the poly Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/NablaRepApply.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/NablaRepApply.lean#L79-L80

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_SatakeDualWeyl_NablaRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG

theorem Formalism.UG.polyRep_apply (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (g : GL n O) : polyRep O n g = (polyAct O n g).toLinearMap := by sorry
