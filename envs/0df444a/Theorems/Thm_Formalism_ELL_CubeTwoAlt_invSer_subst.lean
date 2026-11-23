-- Prove2me | Theorems.Thm_Formalism_ELL_CubeTwoAlt_invSer_subst
-- name    : Formalism.ELL.CubeTwoAlt.invSer_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:39.82918+00:00
-- url     : https://prove2.me/theorems/b16ebca9-d16f-4806-9aea-901d5cba7aeb
-- title:
--   Cube Two Alt: inv Ser subst
-- statement:
--   The Cube Two Alt construction uses the inv Ser subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L179-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean#L179-L202

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

theorem Formalism.ELL.CubeTwoAlt.invSer_subst (hw : WFixed W w) (i : Fin 2) :
    (invSer W w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X i * (dI W w i)⁻¹ := by sorry
