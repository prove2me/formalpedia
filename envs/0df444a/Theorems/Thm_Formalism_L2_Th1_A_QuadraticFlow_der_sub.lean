-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_sub
-- name    : Formalism.L2.Th1.A.QuadraticFlow.der_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:19.652026+00:00
-- url     : https://prove2.me/theorems/7b9bb136-e8c7-4542-8289-7a74c1dd98f4
-- title:
--   Quadratic Flow: der sub
-- statement:
--   The Quadratic Flow construction uses the der sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowTwo.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowTwo.lean#L29-L30

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
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
open Formalism.L2.Th1.A.QuadraticFlow
variable {A : Type u} [CommRing A] {D : A → A}

theorem Formalism.L2.Th1.A.QuadraticFlow.der_sub (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by sorry
