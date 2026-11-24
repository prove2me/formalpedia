-- Prove2me | Theorems.Thm_Formalism_UG_P_spherical_qV_ne_zero
-- name    : Formalism.UG.P.spherical_qV_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:51.234708+00:00
-- url     : https://prove2.me/theorems/a6a1223a-e26e-45e3-8781-48e3f1d96f7b
-- title:
--   P: spherical q V ne zero
-- statement:
--   The P construction uses the spherical q V ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L75-L77

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.UG.P.spherical_qV_ne_zero : (qV F v : ℂ) ≠ 0 := by sorry
