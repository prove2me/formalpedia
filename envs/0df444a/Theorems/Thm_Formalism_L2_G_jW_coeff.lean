-- Prove2me | Theorems.Thm_Formalism_L2_G_jW_coeff
-- name    : Formalism.L2.G.jW_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:58.355253+00:00
-- url     : https://prove2.me/theorems/64ae7d45-2c59-4875-88b4-b9476ee5b398
-- title:
--   G: j W coeff
-- statement:
--   The G construction uses the j W coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L177-L178

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]

theorem Formalism.L2.G.jW_coeff (x : WQ p n) (k : ℕ) : (jW p n x).coeff k = algebraMap (F1 p n) (F2 p n) (x.coeff k) := by sorry
