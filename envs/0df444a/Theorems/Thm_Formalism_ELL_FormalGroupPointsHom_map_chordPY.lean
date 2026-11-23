-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_chordPY
-- name    : Formalism.ELL.FormalGroupPointsHom.map_chordPY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:39.858421+00:00
-- url     : https://prove2.me/theorems/6068a39a-3b11-4343-8ecf-2cb04ecc4967
-- title:
--   Formal Group Points Hom: map chord PY
-- statement:
--   The Formal Group Points Hom construction uses the map chord PY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L497-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L497-L499

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

theorem Formalism.ELL.FormalGroupPointsHom.map_chordPY (a1 a3 z1 z2 w1 w2 c v : R) :
    f (chordPY a1 a3 z1 z2 w1 w2 c v) = chordPY (f a1) (f a3) (f z1) (f z2) (f w1) (f w2) (f c) (f v) := by sorry
