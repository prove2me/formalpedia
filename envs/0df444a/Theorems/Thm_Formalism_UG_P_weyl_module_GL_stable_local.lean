-- Prove2me | Theorems.Thm_Formalism_UG_P_weyl_module_GL_stable_local
-- name    : Formalism.UG.P.weyl_module_GL_stable_local
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:38:12.729624+00:00
-- url     : https://prove2.me/theorems/118f9018-489c-49a8-982d-3aadf23b1246
-- title:
--   P: weyl module GL stable local
-- statement:
--   The P construction uses the weyl module GL stable local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L572-L572
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L572-L572

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility

theorem Formalism.UG.P.weyl_module_GL_stable_local : Formalism.UG.WeylGLStableLocal := by sorry
