-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_weq_C
-- name    : Formalism.ELL.FormalGroupPointsHom.weq_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:50.009276+00:00
-- url     : https://prove2.me/theorems/38825ddc-722a-4b3c-8ed0-005d8cee27cc
-- title:
--   Formal Group Points Hom: weq C
-- statement:
--   The Formal Group Points Hom construction uses the weq C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L572-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L572-L577

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

theorem Formalism.ELL.FormalGroupPointsHom.weq_C {W : WeierstrassCurve K} {σ : Type} {s v : MvPowerSeries σ K} (h : WEqAt W s v) :
    v = s ^ 3 + MvPowerSeries.C W.a₁ * (s * v) + MvPowerSeries.C W.a₂ * (s ^ 2 * v)
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * (s * v ^ 2)
      + MvPowerSeries.C W.a₆ * v ^ 3 := by sorry
