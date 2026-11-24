-- Prove2me | Theorems.Thm_Formalism_L2_G_sq_lift
-- name    : Formalism.L2.G.sq_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:45.787591+00:00
-- url     : https://prove2.me/theorems/ee443a5c-7ae3-4e19-90f4-786d3539b216
-- title:
--   G: sq lift
-- statement:
--   The G construction uses the sq lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L420-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L420-L449

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

theorem Formalism.L2.G.sq_lift (c : W2 p n) (y0 : F2 p n) (hc : c.coeff 0 = y0 * y0) (hy00 : y0 ≠ 0)
    (h2 : (2 : F2 p n) ≠ 0) : ∃ y : W2 p n, y ^ 2 = c := by sorry
