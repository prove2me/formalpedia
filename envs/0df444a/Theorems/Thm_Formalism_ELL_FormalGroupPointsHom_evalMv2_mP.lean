-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_mP
-- name    : Formalism.ELL.FormalGroupPointsHom.evalMv2_mP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:30.71539+00:00
-- url     : https://prove2.me/theorems/7d200f5e-e5a6-4336-b6eb-b4c38e0ba31a
-- title:
--   Formal Group Points Hom: eval Mv2 m P
-- statement:
--   The Formal Group Points Hom construction uses the eval Mv2 m P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L855-L859
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L855-L859

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

theorem Formalism.ELL.FormalGroupPointsHom.evalMv2_mP {a1 a3 z w : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a3) (h3 : IntegralMv z) (h4 : IntegralMv w) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (mP a1 a3 z w) a b = mP (evalMv2 a1 a b) (evalMv2 a3 a b) (evalMv2 z a b) (evalMv2 w a b) := by sorry
