-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_exponent
-- name    : Formalism.UG.P.satake_exponent
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:14.05938+00:00
-- url     : https://prove2.me/theorems/055f0aaa-5325-4368-b03a-2f6ce7a09cc1
-- title:
--   P: satake exponent
-- statement:
--   The P construction uses the satake exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L97-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L97-L112

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
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
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem Formalism.UG.P.satake_exponent (α : Fin n → ℂ) (S : Finset (Fin n)) :
    ((qV F v : ℂ)) ^ satakeInv Finset.univ S *
      ∏ a ∈ S, (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2))) =
      (qV F v : ℂ) ^ (((S.card : ℂ) * ((n : ℂ) - S.card)) / 2) * ∏ a ∈ S, α a := by sorry
