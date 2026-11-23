-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_tanPY
-- name    : Formalism.ELL.FormalGroupPointsHom.map_tanPY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:31.729274+00:00
-- url     : https://prove2.me/theorems/ddd87203-8991-46f6-b5b2-5538a982a8a0
-- title:
--   Formal Group Points Hom: map tan PY
-- statement:
--   The Formal Group Points Hom construction uses the map tan PY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L505-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L505-L507

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
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem Formalism.ELL.FormalGroupPointsHom.map_tanPY (a1 a2 a3 a4 z w c v : R) :
    f (tanPY a1 a2 a3 a4 z w c v) = tanPY (f a1) (f a2) (f a3) (f a4) (f z) (f w) (f c) (f v) := by sorry
