-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_unif_inv_not_mem
-- name    : Formalism.UG.P.satake_unif_inv_not_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:34:38.872744+00:00
-- url     : https://prove2.me/theorems/90f62190-93c0-47f3-8218-7bcc6553e422
-- title:
--   P: satake unif inv not mem
-- statement:
--   The P construction uses the satake unif inv not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeRes.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeRes.lean#L39-L48

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.UG.P.satake_unif_inv_not_mem {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ⁻¹ ∉ Ov F v := by sorry
