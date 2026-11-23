-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_mem_Ov
-- name    : Formalism.UG.P.cartan_mem_Ov
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:10.731288+00:00
-- url     : https://prove2.me/theorems/f4a25041-cbbb-44dd-8c11-0f61e75edf83
-- title:
--   P: cartan mem Ov
-- statement:
--   The P construction uses the cartan mem Ov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L341-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L341-L345

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open IsDedekindDomain NumberField

theorem Formalism.UG.P.cartan_mem_Ov (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by sorry
