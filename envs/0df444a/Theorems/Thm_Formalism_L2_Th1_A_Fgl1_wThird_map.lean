-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wThird_map
-- name    : Formalism.L2.Th1.A.Fgl1.wThird_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:13.050489+00:00
-- url     : https://prove2.me/theorems/5173499d-7fa0-4625-945c-32829d3ac939
-- title:
--   Fgl1: w Third map
-- statement:
--   The Fgl1 construction uses the w Third map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L368-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L368-L369

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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)

theorem Formalism.L2.Th1.A.Fgl1.wThird_map : MvPowerSeries.map φ (wThird W) = wThird (W.map φ) := by sorry
