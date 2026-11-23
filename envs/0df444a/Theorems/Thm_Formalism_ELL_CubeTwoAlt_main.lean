-- Prove2me | Theorems.Thm_Formalism_ELL_CubeTwoAlt_main
-- name    : Formalism.ELL.CubeTwoAlt.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:22.561811+00:00
-- url     : https://prove2.me/theorems/f1ac82b2-7a29-4a3c-af9c-708e2820e135
-- title:
--   Cube Two Alt: main
-- statement:
--   The Cube Two Alt construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L303-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L303-L403

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
variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}
local notation "cc" => MvPowerSeries.constantCoeff

theorem Formalism.ELL.CubeTwoAlt.main (hw : WFixed W w) :
    ∃ c : MvPowerSeries (Fin 2) K, c ∈ T W ∧ cc c = -1 ∧
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))⁻¹
        - (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))⁻¹
        = c * WeierstrassChordSeries.F2 W w * MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
            (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] (WeierstrassChordSeries.F2 W w) := by sorry
