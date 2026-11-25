-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_adelic_level_commute
-- name    : Formalism.UG.P.finite_adelic_level_commute
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:55.346203+00:00
-- url     : https://prove2.me/theorems/454adbe6-dd56-5591-928c-aa9ebb648e85
-- title:
--   P: finite adelic level commute
-- statement:
--   The P construction uses the finite adelic level commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L446-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L446-L495

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct

theorem Formalism.UG.P.finite_adelic_level_commute : Formalism.UG.LevelAfComm := by sorry
