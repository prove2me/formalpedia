-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitIE_tmul
-- name    : Formalism.UG.P.afsplitIE_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:13.368949+00:00
-- url     : https://prove2.me/theorems/9d32436a-ed9f-41d9-8097-b3060e18aff5
-- title:
--   P: afsplit IE tmul
-- statement:
--   The P construction uses the afsplit IE tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L29-L30

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

theorem Formalism.UG.P.afsplitIE_tmul (v : HeightOneSpectrum (𝓞 F)) (a : E) (x : v.adicCompletion F) :
    afsplitIE v (a ⊗ₜ[F] x) = a ⊗ₜ[F] afsplitI v x := by sorry
