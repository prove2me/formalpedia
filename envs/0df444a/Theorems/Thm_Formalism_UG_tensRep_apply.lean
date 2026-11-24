-- Prove2me | Theorems.Thm_Formalism_UG_tensRep_apply
-- name    : Formalism.UG.tensRep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:20.868439+00:00
-- url     : https://prove2.me/theorems/c6606a6c-22fa-45da-b163-f2ae1bbf9cf8
-- title:
--   UG: tens Rep apply
-- statement:
--   The UG construction uses the tens Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/NablaRepApply.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/NablaRepApply.lean#L76-L77

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

theorem Formalism.UG.tensRep_apply (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
    (g : GL n O) : tensRep O n k g = tensAct O n k g := by sorry
