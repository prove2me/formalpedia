-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_subst
-- name    : Formalism.ELL.FormalGroupPointsHom.evalMv2_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:07.394035+00:00
-- url     : https://prove2.me/theorems/b3f848e0-c6eb-4f25-b5fa-8261d26955c4
-- title:
--   Formal Group Points Hom: eval Mv2 subst
-- statement:
--   The Formal Group Points Hom construction uses the eval Mv2 subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L210-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L210-L276

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

theorem Formalism.ELL.FormalGroupPointsHom.evalMv2_subst {G s t : MvPowerSeries (Fin 2) K} (hG : IntegralMv G) (hs : IntegralMv s)
    (ht : IntegralMv t) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (G.subst ![s, t]) a b = evalMv2 G (evalMv2 s a b) (evalMv2 t a b) := by sorry
