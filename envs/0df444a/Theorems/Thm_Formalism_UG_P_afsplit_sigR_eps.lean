-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_sigR_eps
-- name    : Formalism.UG.P.afsplit_sigR_eps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:31.48809+00:00
-- url     : https://prove2.me/theorems/0380b7a5-ac7f-4a69-9d9f-5c7ee3c67a34
-- title:
--   P: afsplit sig R eps
-- statement:
--   The P construction uses the afsplit sig R eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L84-L86

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

theorem Formalism.UG.P.afsplit_sigR_eps (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    sigR σ 𝔸 (afsplitEps E v) = afsplitEps E v := by sorry
