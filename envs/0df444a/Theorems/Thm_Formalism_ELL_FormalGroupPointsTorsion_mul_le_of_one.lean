-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mul_le_of_one
-- name    : Formalism.ELL.FormalGroupPointsTorsion.mul_le_of_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:11.417095+00:00
-- url     : https://prove2.me/theorems/4ce2f026-f86f-4155-b6ac-cd3ec30dbb29
-- title:
--   Formal Group Points Torsion: mul le of one
-- statement:
--   The Formal Group Points Torsion construction uses the mul le of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L30-L31

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

theorem Formalism.ELL.FormalGroupPointsTorsion.mul_le_of_one {a b : K} (ha : ‖a‖ ≤ 1) : ‖a * b‖ ≤ ‖b‖ := by sorry
