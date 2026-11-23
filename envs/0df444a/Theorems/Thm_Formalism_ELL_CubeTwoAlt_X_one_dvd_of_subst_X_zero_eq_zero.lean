-- Prove2me | Theorems.Thm_Formalism_ELL_CubeTwoAlt_X_one_dvd_of_subst_X_zero_eq_zero
-- name    : Formalism.ELL.CubeTwoAlt.X_one_dvd_of_subst_X_zero_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:45.269749+00:00
-- url     : https://prove2.me/theorems/531e8cc9-0245-46ee-b0ab-3325aba93f47
-- title:
--   Cube Two Alt: X one dvd of subst X zero eq zero
-- statement:
--   The Cube Two Alt construction uses the X one dvd of subst X zero eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L52-L57

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

theorem Formalism.ELL.CubeTwoAlt.X_one_dvd_of_subst_X_zero_eq_zero (H : MvPowerSeries (Fin 2) K)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = 0) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by sorry
