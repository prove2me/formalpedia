-- Prove2me | Theorems.Thm_Formalism_ELL_CubeThreeAlt_det_rows
-- name    : Formalism.ELL.CubeThreeAlt.det_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:29.691584+00:00
-- url     : https://prove2.me/theorems/0c23827f-0a54-4bba-b21d-ba8303f6c61e
-- title:
--   Cube Three Alt: det rows
-- statement:
--   The Cube Three Alt construction uses the det rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L56-L63

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

theorem Formalism.ELL.CubeThreeAlt.det_rows (t V ww : Fin 3 → R) (h : ∀ i, t i ^ 3 = V i * ww i) :
    (Matrix.of fun i => ![t i ^ 3, t i * V i, -V i]).det
      = -(V 0 * V 1 * V 2) * ((ww 1 - ww 0) * (t 2 - t 0) - (ww 2 - ww 0) * (t 1 - t 0)) := by sorry
