-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_mem_lat
-- name    : Formalism.UG.P.levelv_mem_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:54.611379+00:00
-- url     : https://prove2.me/theorems/837a1a71-e695-4c4c-b8b1-26e8b65cd460
-- title:
--   P: levelv mem lat
-- statement:
--   The P construction uses the levelv mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L214-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L214-L221

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
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelv_mem_lat (x : n → E ⊗[F] v.adicCompletion F) :
    x ∈ stdLat (n := n) ↥(lvS F E v) ↔ ∀ j, x j ∈ lvS F E v := by sorry
