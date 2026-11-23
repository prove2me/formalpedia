-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_x_X0_ne_x_X1
-- name    : Formalism.ELL.FormalGroupPointsHom.x_X0_ne_x_X1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:53.146502+00:00
-- url     : https://prove2.me/theorems/750071f7-19fe-4054-8a7d-a4b0509165f2
-- title:
--   Formal Group Points Hom: x X0 ne x X1
-- statement:
--   The Formal Group Points Hom construction uses the x X0 ne x X1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L561-L570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L561-L570

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

theorem Formalism.ELL.FormalGroupPointsHom.x_X0_ne_x_X1 {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w (MvPowerSeries.X 1) := by sorry
