-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_mP
-- name    : Formalism.ELL.FormalGroupPointsHom.map_mP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:52.638164+00:00
-- url     : https://prove2.me/theorems/d79b4860-9be5-41a0-931a-32e3f80e0916
-- title:
--   Formal Group Points Hom: map m P
-- statement:
--   The Formal Group Points Hom construction uses the map m P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L513-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L513-L514

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

theorem Formalism.ELL.FormalGroupPointsHom.map_mP (a1 a3 z w : R) : f (mP a1 a3 z w) = mP (f a1) (f a3) (f z) (f w) := by sorry
