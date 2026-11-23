-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
-- name    : Formalism.L2.Th1.A.IsDer.map_ofNat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:10.245444+00:00
-- url     : https://prove2.me/theorems/11fea41c-7ae2-4767-8acb-f08c403d5c93
-- title:
--   Is Der: map of Nat
-- statement:
--   The Is Der construction uses the map of Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean#L44-L46

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

theorem Formalism.L2.Th1.A.IsDer.map_ofNat (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by sorry
