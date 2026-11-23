-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
-- name    : Formalism.L2.Th1.A.ISer.subHom_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:47.59267+00:00
-- url     : https://prove2.me/theorems/467a8662-2df5-44e0-b635-eb33f5eb961f
-- title:
--   ISer: sub Hom C
-- statement:
--   The ISer construction uses the sub Hom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean#L26-L28

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

theorem Formalism.L2.Th1.A.ISer.subHom_C (s : R⟦X⟧) (hs : constantCoeff s = 0) (a : R) : subHom s hs (C a) = C a := by sorry
