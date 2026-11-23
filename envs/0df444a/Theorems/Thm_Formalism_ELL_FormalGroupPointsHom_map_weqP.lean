-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_weqP
-- name    : Formalism.ELL.FormalGroupPointsHom.map_weqP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:11:32.624553+00:00
-- url     : https://prove2.me/theorems/d6955bd0-7c87-45c0-8e0e-f7843314a7f1
-- title:
--   Formal Group Points Hom: map weq P
-- statement:
--   The Formal Group Points Hom construction uses the map weq P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L509-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L509-L511

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

theorem Formalism.ELL.FormalGroupPointsHom.map_weqP (a1 a2 a3 a4 a6 s v : R) :
    f (weqP a1 a2 a3 a4 a6 s v) = weqP (f a1) (f a2) (f a3) (f a4) (f a6) (f s) (f v) := by sorry
