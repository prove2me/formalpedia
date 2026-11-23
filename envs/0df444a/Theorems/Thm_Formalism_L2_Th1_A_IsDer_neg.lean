-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_IsDer_neg
-- name    : Formalism.L2.Th1.A.IsDer.neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:59.005924+00:00
-- url     : https://prove2.me/theorems/bd87de41-0327-4ea5-9d6a-c4cddd2ae88a
-- title:
--   Is Der: neg
-- statement:
--   The Is Der construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L73-L81

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.IsDer
variable {A : Type u} [CommRing A] {D : A → A}

theorem Formalism.L2.Th1.A.IsDer.neg (h : IsDer D) : IsDer (fun a => -D a) := by sorry
