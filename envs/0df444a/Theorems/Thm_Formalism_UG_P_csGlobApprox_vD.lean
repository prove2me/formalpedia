-- Prove2me | Theorems.Thm_Formalism_UG_P_csGlobApprox_vD
-- name    : Formalism.UG.P.csGlobApprox_vD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:51.772813+00:00
-- url     : https://prove2.me/theorems/15490bf1-c1e7-4f5a-b6a0-f592b746bdab
-- title:
--   P: cs Glob Approx v D
-- statement:
--   The P construction uses the cs Glob Approx v D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsGlobApprox.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsGlobApprox.lean#L15-L21

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.UG.P.csGlobApprox_vD (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by sorry
