-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_chord_iff
-- name    : Formalism.ELL.FormalGroupPointsHom.chord_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:31.007307+00:00
-- url     : https://prove2.me/theorems/0c83924f-b9d9-4dcf-87c9-020da643f814
-- title:
--   Formal Group Points Hom: chord iff
-- statement:
--   The Formal Group Points Hom construction uses the chord iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L434-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L434-L456

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
variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)

theorem Formalism.ELL.FormalGroupPointsHom.chord_iff {z1 z2 w1 w2 c v : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) (hv : v ≠ 0) :
    (c / v = W.addX (z1 / w1) (z2 / w2) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2)) ∧
      -1 / v = W.addY (z1 / w1) (z2 / w2) (-1 / w1) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2))) ↔
    (chordPX W.a₁ W.a₂ z1 z2 w1 w2 c v = 0 ∧ chordPY W.a₁ W.a₃ z1 z2 w1 w2 c v = 0) := by sorry
