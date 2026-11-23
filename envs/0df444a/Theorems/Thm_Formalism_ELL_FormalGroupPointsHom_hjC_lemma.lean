-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hjC_lemma
-- name    : Formalism.ELL.FormalGroupPointsHom.hjC_lemma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:19.611769+00:00
-- url     : https://prove2.me/theorems/d0e15285-331a-45f0-9863-04f217b2c96e
-- title:
--   Formal Group Points Hom: hj C lemma
-- statement:
--   The Formal Group Points Hom construction uses the hj C lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L897-L901
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L897-L901

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

theorem Formalism.ELL.FormalGroupPointsHom.hjC_lemma {σ : Type} (a : K) :
    algebraMap K (FractionRing (MvPowerSeries σ K)) a =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (MvPowerSeries.C a) := by sorry
