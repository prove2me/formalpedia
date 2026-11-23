-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_lt
-- name    : Formalism.ELL.FormalGroupPointsTorsion.sub_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:02.171578+00:00
-- url     : https://prove2.me/theorems/c024b52b-57f4-4f9b-a851-63c808f53452
-- title:
--   Formal Group Points Torsion: sub lt
-- statement:
--   The Formal Group Points Torsion construction uses the sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L23-L24

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.FormalGroupPointsTorsion.sub_lt {a b : K} {c : ℝ} (ha : ‖a‖ < c) (hb : ‖b‖ < c) : ‖a - b‖ < c := by sorry
