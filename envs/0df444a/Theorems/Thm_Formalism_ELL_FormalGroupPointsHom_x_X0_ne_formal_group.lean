-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_x_X0_ne_formal_group
-- name    : Formalism.ELL.FormalGroupPointsHom.x_X0_ne_formal_group
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:43.393835+00:00
-- url     : https://prove2.me/theorems/30358d7b-abaf-4371-b4cf-7c2306b495e3
-- title:
--   Formal Group Points Hom: x X0 ne formal group
-- statement:
--   The Formal Group Points Hom construction uses the x X0 ne formal group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L548-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L548-L559

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
variable {K : Type u} [Field K]

theorem Formalism.ELL.FormalGroupPointsHom.x_X0_ne_formal_group {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w)
    (F : FormalGroup K) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w F.toPowerSeries := by sorry
