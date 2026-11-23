-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_S_le_range
-- name    : Formalism.UG.P.levelv_S_le_range
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:09.812969+00:00
-- url     : https://prove2.me/theorems/b9e756f1-d08e-4683-9033-d0e4a6ed25be
-- title:
--   P: levelv S le range
-- statement:
--   The P construction uses the levelv S le range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L122-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L122-L136

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

theorem Formalism.UG.P.levelv_S_le_range (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ lvS F E v) :
    y ∈ (levelvPsi F E v).range := by sorry
