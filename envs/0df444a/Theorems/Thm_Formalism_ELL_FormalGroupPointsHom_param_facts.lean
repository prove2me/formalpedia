-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_param_facts
-- name    : Formalism.ELL.FormalGroupPointsHom.param_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:44.727093+00:00
-- url     : https://prove2.me/theorems/4b46057f-4c48-4142-b0c9-054ec17f0e0f
-- title:
--   Formal Group Points Hom: param facts
-- statement:
--   The Formal Group Points Hom construction uses the param facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1143-L1149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1143-L1149

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem Formalism.ELL.FormalGroupPointsHom.param_facts (hPar : FormalGroupPointsParametrisation.{u}) {W : WeierstrassCurve K} {w : PowerSeries K}
    (hW : IntegralModel W) (hw : WFixed W w) {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : 1 < ‖x‖) :
    ‖-x / y‖ < 1 ∧ evalPS w (-x / y) ≠ 0 ∧ x = (-x / y) / evalPS w (-x / y) ∧
      y = -1 / evalPS w (-x / y) := by sorry
