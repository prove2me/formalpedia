-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_mulVec_injective
-- name    : Formalism.UG.P.cartan_mulVec_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:49.832464+00:00
-- url     : https://prove2.me/theorems/adbe4896-aa4c-431b-8f10-c859cbf88e74
-- title:
--   P: cartan mul Vec injective
-- statement:
--   The P construction uses the cartan mul Vec injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L13-L18

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.cartan_mulVec_injective (G : Matrix n n R) (hG : G.det ≠ 0) :
    Function.Injective (Matrix.mulVecLin G) := by sorry
