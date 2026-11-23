-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_chordPX
-- name    : Formalism.ELL.FormalGroupPointsHom.map_chordPX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:03.07943+00:00
-- url     : https://prove2.me/theorems/617972a4-d2fa-49e8-943e-7135abb081a4
-- title:
--   Formal Group Points Hom: map chord PX
-- statement:
--   The Formal Group Points Hom construction uses the map chord PX property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L493-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L493-L495

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

theorem Formalism.ELL.FormalGroupPointsHom.map_chordPX (a1 a2 z1 z2 w1 w2 c v : R) :
    f (chordPX a1 a2 z1 z2 w1 w2 c v) = chordPX (f a1) (f a2) (f z1) (f z2) (f w1) (f w2) (f c) (f v) := by sorry
