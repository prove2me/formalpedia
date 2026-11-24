-- Prove2me | Theorems.Thm_Formalism_L2_G_jW_injective
-- name    : Formalism.L2.G.jW_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:22.339407+00:00
-- url     : https://prove2.me/theorems/f1646f0b-78a7-4003-850e-da2cff980ddb
-- title:
--   G: j W injective
-- statement:
--   The G construction uses the j W injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L181-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L181-L186

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

theorem Formalism.L2.G.jW_injective : Function.Injective (jW p n) := by sorry
