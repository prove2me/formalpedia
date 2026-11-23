-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_sub_apply
-- name    : Formalism.UG.P.afsplit_sub_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:12.020735+00:00
-- url     : https://prove2.me/theorems/80ce5ff4-04da-4d20-8709-471f7fdbe13e
-- title:
--   P: afsplit sub apply
-- statement:
--   The P construction uses the afsplit sub apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L16-L16

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

theorem Formalism.UG.P.afsplit_sub_apply (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := by sorry
