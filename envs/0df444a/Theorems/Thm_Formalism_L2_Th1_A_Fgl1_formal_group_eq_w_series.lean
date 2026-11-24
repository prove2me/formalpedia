-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_formal_group_eq_w_series
-- name    : Formalism.L2.Th1.A.Fgl1.formal_group_eq_w_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:16.344303+00:00
-- url     : https://prove2.me/theorems/fa8a8a28-3521-4fd0-b62d-88c19f0a23ea
-- title:
--   Fgl1: formal group eq w series
-- statement:
--   The Fgl1 construction uses the formal group eq w series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L443-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L443-L454

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
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
open Formalism.ELL.WeierstrassChordSeries (z3 w3 F2)

theorem Formalism.L2.Th1.A.Fgl1.formal_group_eq_w_series : fgl W = F2 W (wSer W) := by sorry
