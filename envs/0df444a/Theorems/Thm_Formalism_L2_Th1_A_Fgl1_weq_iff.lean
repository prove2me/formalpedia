-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_weq_iff
-- name    : Formalism.L2.Th1.A.Fgl1.weq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:05.407601+00:00
-- url     : https://prove2.me/theorems/6feadcad-b9f4-445e-ae7d-24b70901a439
-- title:
--   Fgl1: weq iff
-- statement:
--   The Fgl1 construction uses the weq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L178-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L178-L187

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_weq_iff

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
open Formalism.ELL.WeierstrassChordSeries

theorem Formalism.L2.Th1.A.Fgl1.weq_iff (W : WeierstrassCurve R) (s v : MvPowerSeries (Fin 2) R) :
    Formalism.ELL.WEqAt W s v ↔ G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) s v = 0 := by sorry
