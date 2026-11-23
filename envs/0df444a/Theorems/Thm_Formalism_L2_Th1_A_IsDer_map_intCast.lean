-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_intCast
-- name    : Formalism.L2.Th1.A.IsDer.map_intCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:09.768599+00:00
-- url     : https://prove2.me/theorems/a446ad86-916e-427e-8607-e2684e475081
-- title:
--   Is Der: map int Cast
-- statement:
--   The Is Der construction uses the map int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L38-L42

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

theorem Formalism.L2.Th1.A.IsDer.map_intCast (h : IsDer D) (n : ℤ) : D (n : A) = 0 := by sorry
