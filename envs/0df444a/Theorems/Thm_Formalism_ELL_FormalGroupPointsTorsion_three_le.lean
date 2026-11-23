-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_three_le
-- name    : Formalism.ELL.FormalGroupPointsTorsion.three_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:38.096881+00:00
-- url     : https://prove2.me/theorems/f3deb1c2-e4dc-486d-a96a-113745e71efb
-- title:
--   Formal Group Points Torsion: three le
-- statement:
--   The Formal Group Points Torsion construction uses the three le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L36-L37

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

theorem Formalism.ELL.FormalGroupPointsTorsion.three_le : ‖(3 : K)‖ ≤ 1 := by sorry
