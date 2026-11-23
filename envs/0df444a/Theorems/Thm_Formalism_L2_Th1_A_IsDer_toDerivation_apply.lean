-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
-- name    : Formalism.L2.Th1.A.IsDer.toDerivation_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:36.590351+00:00
-- url     : https://prove2.me/theorems/8b3b881d-9908-4aee-8b98-f2aefbe2a564
-- title:
--   Is Der: to Derivation apply
-- statement:
--   The Is Der construction uses the to Derivation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L87-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L87-L87

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

theorem Formalism.L2.Th1.A.IsDer.toDerivation_apply (h : IsDer D) (a : A) : h.toDerivation a = D a := by sorry

attribute [defeq] Formalism.L2.Th1.A.IsDer.toDerivation_apply
