-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_one_apply
-- name    : Formalism.UG.P.afsplit_one_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:06.517783+00:00
-- url     : https://prove2.me/theorems/5d409f0c-1bbd-488f-92b1-1ddf43e46c68
-- title:
--   P: afsplit one apply
-- statement:
--   The P construction uses the afsplit one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L17-L17

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
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
variable {F : Type} [Field F] [NumberField F]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.UG.P.afsplit_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸) w = 1 := by sorry
