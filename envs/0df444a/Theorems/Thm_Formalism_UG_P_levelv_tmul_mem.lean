-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_tmul_mem
-- name    : Formalism.UG.P.levelv_tmul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:18.003786+00:00
-- url     : https://prove2.me/theorems/e084002b-f3b8-4548-8d77-9805acde7e69
-- title:
--   P: levelv tmul mem
-- statement:
--   The P construction uses the levelv tmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L57-L65

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

theorem Formalism.UG.P.levelv_tmul_mem (e : E) (he : e ∈ intOE E) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : e ⊗ₜ[F] x ∈ lvS F E v := by sorry
