-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_zero_apply
-- name    : Formalism.UG.P.afsplit_zero_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:17.797796+00:00
-- url     : https://prove2.me/theorems/4d555775-97e6-4337-bd40-e5b55557e594
-- title:
--   P: afsplit zero apply
-- statement:
--   The P construction uses the afsplit zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L18-L18

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

theorem Formalism.UG.P.afsplit_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸) w = 0 := by sorry
