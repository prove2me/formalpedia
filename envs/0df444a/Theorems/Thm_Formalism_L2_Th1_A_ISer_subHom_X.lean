-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_X
-- name    : Formalism.L2.Th1.A.ISer.subHom_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:19.379484+00:00
-- url     : https://prove2.me/theorems/77eb9ae9-8692-4a27-bd25-3d215d2aaaed
-- title:
--   ISer: sub Hom X
-- statement:
--   The ISer construction uses the sub Hom X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean#L23-L24

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
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
open Formalism.L2.Th1.A.ISer
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.ISer.subHom_X (s : R⟦X⟧) (hs : constantCoeff s = 0) : subHom s hs X = s := by sorry
