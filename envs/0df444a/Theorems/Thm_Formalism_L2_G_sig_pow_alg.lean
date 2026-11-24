-- Prove2me | Theorems.Thm_Formalism_L2_G_sig_pow_alg
-- name    : Formalism.L2.G.sig_pow_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:41.106811+00:00
-- url     : https://prove2.me/theorems/bc69e404-5606-48db-9119-55d809760b12
-- title:
--   G: sig pow alg
-- statement:
--   The G construction uses the sig pow alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L109-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L109-L116

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

theorem Formalism.L2.G.sig_pow_alg (k : ℕ) (x : WQ p n) :
    (sig p n ^ k) (algebraMap _ _ x) = algebraMap _ _ ((WittVector.frobenius^[k]) x) := by sorry
