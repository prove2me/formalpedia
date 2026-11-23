-- Prove2me | Theorems.Thm_Formalism_UG_P_csGlobApprox_local
-- name    : Formalism.UG.P.csGlobApprox_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:22.040658+00:00
-- url     : https://prove2.me/theorems/7b553237-afe5-4dd3-a325-d7c1fb374560
-- title:
--   P: cs Glob Approx local
-- statement:
--   The P construction uses the cs Glob Approx local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsGlobApprox.lean#L23-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsGlobApprox.lean#L23-L63

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

theorem Formalism.UG.P.csGlobApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by sorry
