-- Prove2me | Theorems.Thm_Formalism_L2_G_jW_finite
-- name    : Formalism.L2.G.jW_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:32.264533+00:00
-- url     : https://prove2.me/theorems/2b450a26-f8af-4406-a97e-0e7090dfb207
-- title:
--   G: j W finite
-- statement:
--   The G construction uses the j W finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L295-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L295-L395

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

theorem Formalism.L2.G.jW_finite : (jW p n).Finite := by sorry
