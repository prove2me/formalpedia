-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeB_upper
-- name    : Formalism.UG.P.satakeB_upper
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:47.312203+00:00
-- url     : https://prove2.me/theorems/40adc746-faf1-4aa0-9f2b-1012bf65eac0
-- title:
--   P: satake B upper
-- statement:
--   The P construction uses the satake B upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L133-L134

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)

theorem Formalism.UG.P.satakeB_upper {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) : IsUpperB F v (satakeB v hϖ hu i) := by sorry
