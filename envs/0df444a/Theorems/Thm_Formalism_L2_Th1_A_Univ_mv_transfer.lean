-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Univ_mv_transfer
-- name    : Formalism.L2.Th1.A.Univ.mv_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:35.362902+00:00
-- url     : https://prove2.me/theorems/1f2d40d2-b177-4e59-b032-c908d4468969
-- title:
--   Univ: mv transfer
-- statement:
--   The Univ construction uses the mv transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L53-L56

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
open Formalism.L2.Th1.A.Univ

theorem Formalism.L2.Th1.A.Univ.mv_transfer {σ : Type*} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {A B : MvPowerSeries σ Z} (h : MvPowerSeries.map ι A = MvPowerSeries.map ι B) :
    MvPowerSeries.map (φ_of W) A = MvPowerSeries.map (φ_of W) B := by sorry
