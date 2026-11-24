-- Prove2me | Theorems.Thm_Formalism_UG_P_csApprox_global
-- name    : Formalism.UG.P.csApprox_global
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:19.763979+00:00
-- url     : https://prove2.me/theorems/ea36aa2d-d8c9-48a6-afed-a66ccdd35cc7
-- title:
--   P: cs Approx global
-- statement:
--   The P construction uses the cs Approx global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsApprox.lean#L59-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsApprox.lean#L59-L86

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

theorem Formalism.UG.P.csApprox_global (D : 𝓞 F) (hD : D ≠ 0) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ intAd F) :
    ∃ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by sorry
