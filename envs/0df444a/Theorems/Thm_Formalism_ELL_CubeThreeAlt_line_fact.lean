-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_line_fact
-- name    : Formalism.ELL.CubeThreeAlt.line_fact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:36.148848+00:00
-- url     : https://prove2.me/theorems/0632c9a9-669c-48d3-a804-885f5e7b9f7b
-- title:
--   Cube Three Alt: line fact
-- statement:
--   The Cube Three Alt construction uses the line fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L29-L35

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
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
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {R : Type*} [CommRing R]

theorem Formalism.ELL.CubeThreeAlt.line_fact [IsDomain R] {a1 a2 a3 a4 a6 l n a b z : R} (hab : a ≠ b)
    (ha : G a1 a2 a3 a4 a6 a (l * a + n) = 0) (hb : G a1 a2 a3 a4 a6 b (l * b + n) = 0)
    (he1 : c3 a2 a4 a6 l * (a + b + z) + c2 a1 a2 a3 a4 a6 l n = 0) (c : R) :
    G a1 a2 a3 a4 a6 c (l * c + n) = c3 a2 a4 a6 l * (c - a) * (c - b) * (c - z) := by sorry
