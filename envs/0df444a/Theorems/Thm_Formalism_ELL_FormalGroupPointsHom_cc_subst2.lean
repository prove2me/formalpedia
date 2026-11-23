-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_cc_subst2
-- name    : Formalism.ELL.FormalGroupPointsHom.cc_subst2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:44.623916+00:00
-- url     : https://prove2.me/theorems/579f36d1-143d-43e9-bd3c-303a14a2a76f
-- title:
--   Formal Group Points Hom: cc subst2
-- statement:
--   The Formal Group Points Hom construction uses the cc subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L533-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L533-L537

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

theorem Formalism.ELL.FormalGroupPointsHom.cc_subst2 {G s t : MvPowerSeries (Fin 2) K} (hG : MvPowerSeries.constantCoeff G = 0)
    (hs : MvPowerSeries.constantCoeff s = 0) (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.constantCoeff (G.subst ![s, t]) = 0 := by sorry
