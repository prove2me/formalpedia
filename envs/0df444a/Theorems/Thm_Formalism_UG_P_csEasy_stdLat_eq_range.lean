-- Prove2me | Theorems.Thm_Formalism_UG_P_csEasy_stdLat_eq_range
-- name    : Formalism.UG.P.csEasy_stdLat_eq_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:06.363797+00:00
-- url     : https://prove2.me/theorems/9cc73c67-b7d0-40a7-a409-75b133973ac1
-- title:
--   P: cs Easy std Lat eq range
-- statement:
--   The P construction uses the cs Easy std Lat eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsEasy.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsEasy.lean#L18-L30

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.csEasy_stdLat_eq_range (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n]
    [DecidableEq n] :
    Formalism.UG.stdLat (n := n) (A := E) (𝓞 E) =
      LinearMap.range (LinearMap.pi (fun i : n =>
        (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))) := by sorry
