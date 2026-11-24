-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_sub_cancel
-- name    : Formalism.L2.Th1.A.Fgl1.sub_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:33.962115+00:00
-- url     : https://prove2.me/theorems/233b8ef0-aa65-41d3-8e65-a80c2cec3d2d
-- title:
--   Fgl1: sub cancel
-- statement:
--   The Fgl1 construction uses the sub cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L104-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L104-L158

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem Formalism.L2.Th1.A.Fgl1.sub_cancel {f : MvPowerSeries (Fin 2) R}
    (h : f * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = 0) : f = 0 := by sorry
