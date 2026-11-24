-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_uPow_natCast
-- name    : Formalism.L2.Th1.A.uPow_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:54.738953+00:00
-- url     : https://prove2.me/theorems/c6ad4196-9b3d-4ce9-9c0c-5f9d3152c544
-- title:
--   A: u Pow nat Cast
-- statement:
--   The A construction uses the u Pow nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L72-L75

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.uPow_natCast (n : ℕ) : (uPow (n : ℤ) : LaurentSeries R) = toL (X ^ n) := by sorry
