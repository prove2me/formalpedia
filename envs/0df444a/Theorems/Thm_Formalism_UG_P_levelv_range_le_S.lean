-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_range_le_S
-- name    : Formalism.UG.P.levelv_range_le_S
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:45.034478+00:00
-- url     : https://prove2.me/theorems/2778ed97-55f0-466c-9e7e-88739eeb6b2b
-- title:
--   P: levelv range le S
-- statement:
--   The P construction uses the levelv range le S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L138-L141

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.UG.P.levelv_range_le_S (a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) :
    levelvPsi F E v a ∈ lvS F E v := by sorry
