-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_Wi_cc
-- name    : Formalism.L2.Th1.A.Fgl1.Wi_cc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:00.54304+00:00
-- url     : https://prove2.me/theorems/8e950b0a-fc33-41c5-b27c-7836a498d379
-- title:
--   Fgl1: Wi cc
-- statement:
--   The Fgl1 construction uses the Wi cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L291-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L291-L296

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_Wi_cc

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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem Formalism.L2.Th1.A.Fgl1.Wi_cc (i : Fin 2) : cc (Wi W i) = 0 := by sorry
