-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_subst2
-- name    : Formalism.ELL.FormalGroupPointsHom.integral_subst2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:38.54+00:00
-- url     : https://prove2.me/theorems/a40b8ef9-9b4f-461d-a01d-fd954747d7c6
-- title:
--   Formal Group Points Hom: integral subst2
-- statement:
--   The Formal Group Points Hom construction uses the integral subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L319-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L319-L336

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

theorem Formalism.ELL.FormalGroupPointsHom.integral_subst2 {G s t : MvPowerSeries (Fin 2) K} (hG : IntegralMv G) (hs : IntegralMv s)
    (ht : IntegralMv t) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) : IntegralMv (G.subst ![s, t]) := by sorry
