-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_q_fact
-- name    : Formalism.ELL.CubeThreeAlt.q_fact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:45.303459+00:00
-- url     : https://prove2.me/theorems/1a66d192-3a79-44a1-8faf-0dcf9a2e464c
-- title:
--   Cube Three Alt: q fact
-- statement:
--   The Cube Three Alt construction uses the q fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L37-L54

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

theorem Formalism.ELL.CubeThreeAlt.q_fact [IsDomain R] {a1 a2 a3 a4 a6 u s d l c : R} (hu : u ≠ 0) (hd0 : d ≠ 0)
    (hsd : s * d = u) (hd : d = -1 + a1 * u + a3 * (l * u))
    (hG : G a1 a2 a3 a4 a6 u (l * u) = 0) :
    G a1 a2 a3 a4 a6 c (l * c) = c * c3 a2 a4 a6 l * (c - u) * (c - s) := by sorry
