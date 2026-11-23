-- Prove2me | Theorems.Thm_Formalism_UG_P_csApprox_local
-- name    : Formalism.UG.P.csApprox_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:13.319468+00:00
-- url     : https://prove2.me/theorems/77e105ee-dac0-4bc7-8d7f-c1b076843fb2
-- title:
--   P: cs Approx local
-- statement:
--   The P construction uses the cs Approx local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsApprox.lean#L20-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsApprox.lean#L20-L57

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
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
open scoped WithZero
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.UG.P.csApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) s) < v.intValuation D := by sorry
