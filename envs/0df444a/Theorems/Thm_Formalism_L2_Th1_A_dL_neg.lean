-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_dL_neg
-- name    : Formalism.L2.Th1.A.dL_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:36.212661+00:00
-- url     : https://prove2.me/theorems/8297d607-692d-48b7-8039-b8648cedc476
-- title:
--   A: d L neg
-- statement:
--   The A construction uses the d L neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L233-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L233-L234

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.dL_neg (f : LaurentSeries R) : dL (-f) = - dL f := by sorry
