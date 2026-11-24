-- Prove2me | Theorems.Thm_Formalism_ELL_CubeTwoAlt_Fp_lin
-- name    : Formalism.ELL.CubeTwoAlt.Fp_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:57.452797+00:00
-- url     : https://prove2.me/theorems/df096aaf-02bb-4663-bdf8-b87c8a362ea8
-- title:
--   Cube Two Alt: Fp lin
-- statement:
--   The Cube Two Alt construction uses the Fp lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L271-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L271-L279

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

theorem Formalism.ELL.CubeTwoAlt.Fp_lin (hw : WFixed W w) :
    MvPowerSeries.coeff (Finsupp.single 1 1) ((WeierstrassChordSeries.F2 W w).subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]) = -1 := by sorry
