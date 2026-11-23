-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_Hv_mem
-- name    : Formalism.ELL.CubeThreeAlt.Hv_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:28.895359+00:00
-- url     : https://prove2.me/theorems/f3219abc-bb65-4b58-8c36-691929446684
-- title:
--   Cube Three Alt: Hv mem
-- statement:
--   The Cube Three Alt construction uses the Hv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L65-L72

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

theorem Formalism.ELL.CubeThreeAlt.Hv_mem (T : Subring R) {a1 a2 a3 a4 a6 z v v' : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T)
    (h3 : a3 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hz : z ∈ T) (hv : v ∈ T) (hv' : v' ∈ T) :
    Hv a1 a2 a3 a4 a6 z v v' ∈ T := by sorry
