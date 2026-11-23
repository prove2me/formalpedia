-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_lt
-- name    : Formalism.ELL.FormalGroupPointsTorsion.add_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:25.529594+00:00
-- url     : https://prove2.me/theorems/e8dd95c0-0f20-4026-881e-53d74e2540fd
-- title:
--   Formal Group Points Torsion: add lt
-- statement:
--   The Formal Group Points Torsion construction uses the add lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L20-L21

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

theorem Formalism.ELL.FormalGroupPointsTorsion.add_lt {a b : K} {c : ℝ} (ha : ‖a‖ < c) (hb : ‖b‖ < c) : ‖a + b‖ < c := by sorry
