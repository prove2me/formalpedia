-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_lam_mul
-- name    : Formalism.L2.Th1.A.Fgl1.lam_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:56.193827+00:00
-- url     : https://prove2.me/theorems/a4d24f54-4dca-41a7-934f-f24ab34fb5fc
-- title:
--   Fgl1: lam mul
-- statement:
--   The Fgl1 construction uses the lam mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L278-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L278-L289

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_eq_single_iff
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_mul

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
open Formalism.ELL.WeierstrassChordSeries (eq_single_iff)

theorem Formalism.L2.Th1.A.Fgl1.lam_mul : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam W = Wi W 1 - Wi W 0 := by sorry
