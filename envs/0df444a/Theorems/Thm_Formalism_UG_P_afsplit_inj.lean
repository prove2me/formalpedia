-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_inj
-- name    : Formalism.UG.P.afsplit_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:35.432444+00:00
-- url     : https://prove2.me/theorems/c1a3f267-4c7a-402d-8c32-fe294ff5d86c
-- title:
--   P: afsplit inj
-- statement:
--   The P construction uses the afsplit inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L125-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L125-L146

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.UG.P.afsplit_inj (y : E ⊗[F] 𝔸) (hy : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w y = 0) :
    y = 0 := by sorry
