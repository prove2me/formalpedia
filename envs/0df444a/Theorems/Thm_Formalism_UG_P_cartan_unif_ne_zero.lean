-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_unif_ne_zero
-- name    : Formalism.UG.P.cartan_unif_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:31.208983+00:00
-- url     : https://prove2.me/theorems/ae10e58f-4f59-4e1d-8ed6-59cce9b8ac76
-- title:
--   P: cartan unif ne zero
-- statement:
--   The P construction uses the cartan unif ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L347-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L347-L352

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

theorem Formalism.UG.P.cartan_unif_ne_zero (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by sorry
