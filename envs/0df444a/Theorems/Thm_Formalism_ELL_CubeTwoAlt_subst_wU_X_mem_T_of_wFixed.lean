-- Prove2me | Theorems.Thm_Formalism_ELL_CubeTwoAlt_subst_wU_X_mem_T_of_wFixed
-- name    : Formalism.ELL.CubeTwoAlt.subst_wU_X_mem_T_of_wFixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:08.7307+00:00
-- url     : https://prove2.me/theorems/9803af5b-d2f6-4536-b8d2-5d1ce9d5cb29
-- title:
--   Cube Two Alt: subst w U X mem T of w Fixed
-- statement:
--   The Cube Two Alt construction uses the subst w U X mem T of w Fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L150-L157

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
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
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {w : PowerSeries K}

theorem Formalism.ELL.CubeTwoAlt.subst_wU_X_mem_T_of_wFixed (hw : WFixed W w) (i : Fin 2) :
    (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by sorry
