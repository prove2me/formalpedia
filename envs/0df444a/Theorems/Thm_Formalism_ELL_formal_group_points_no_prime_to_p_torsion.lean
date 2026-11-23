-- Prove2me | Theorems.Thm_Formalism_ELL_formal_group_points_no_prime_to_p_torsion
-- name    : Formalism.ELL.formal_group_points_no_prime_to_p_torsion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:03.261171+00:00
-- url     : https://prove2.me/theorems/8fd06b24-abce-4cec-b52e-e8a89b2a2d97
-- title:
--   ELL: formal group points no prime to p torsion
-- statement:
--   The ELL construction uses the formal group points no prime to p torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L444-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L444-L452

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
open Formalism Formalism.ELL
open WeierstrassCurve
open Classical

theorem Formalism.ELL.formal_group_points_no_prime_to_p_torsion : FormalGroupPointsTorsionFree.{u} := by sorry
