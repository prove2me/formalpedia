-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_prV_tmul
-- name    : Formalism.UG.P.afsplit_prV_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:12.289806+00:00
-- url     : https://prove2.me/theorems/d34e8b2a-96ee-4c2b-9b17-764b49bb389d
-- title:
--   P: afsplit pr V tmul
-- statement:
--   The P construction uses the afsplit pr V tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L32-L33

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

theorem Formalism.UG.P.afsplit_prV_tmul (w : HeightOneSpectrum (𝓞 F)) (a : E) (b : 𝔸) :
    prV (E := E) w (a ⊗ₜ[F] b) = a ⊗ₜ[F] (b w) := by sorry
