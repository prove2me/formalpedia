-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_low
-- name    : Formalism.L2.Th1.A.Fgl1.wSer_low
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:48.987543+00:00
-- url     : https://prove2.me/theorems/c802e8c3-097e-4e00-87e1-797422686ce5
-- title:
--   Fgl1: w Ser low
-- statement:
--   The Fgl1 construction uses the w Ser low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L199-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L199-L218

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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem Formalism.L2.Th1.A.Fgl1.wSer_low : coeff 0 (wSer W) = 0 ∧ coeff 1 (wSer W) = 0 ∧ coeff 2 (wSer W) = 0 ∧
    coeff 3 (wSer W) = 1 := by sorry
