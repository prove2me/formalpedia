-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Two_chordZ
-- name    : Formalism.L2.Th1.A.Two.chordZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:16.18157+00:00
-- url     : https://prove2.me/theorems/14dfce14-5d8a-4fc5-91e0-dc7f5291c3d7
-- title:
--   Two: chord Z
-- statement:
--   The Two construction uses the chord Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L89-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L89-L110

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem Formalism.L2.Th1.A.Two.chordZ {xP yP : K} (hP : W.toAffine.Equation xP yP) :
    toL ((xPlus W xP yP).subst (expSer W)) = (curveL W).toAffine.addX (xZ W) (HahnSeries.C xP)
      ((yZ W - HahnSeries.C yP) * toL ((tS W xP).subst (expSer W))) := by sorry
