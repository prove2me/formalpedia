-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_unif_lt_one
-- name    : Formalism.UG.P.cartan_unif_lt_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:42.063052+00:00
-- url     : https://prove2.me/theorems/5080ba3c-4c65-40cc-aa60-af2f734d7896
-- title:
--   P: cartan unif lt one
-- statement:
--   The P construction uses the cartan unif lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L354-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L354-L361

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

theorem Formalism.UG.P.cartan_unif_lt_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) : Valued.v ϖ < 1 := by sorry
