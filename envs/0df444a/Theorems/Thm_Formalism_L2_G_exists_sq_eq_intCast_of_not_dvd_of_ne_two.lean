-- Prove2me | Theorems.Thm_Formalism_L2_G_exists_sq_eq_intCast_of_not_dvd_of_ne_two
-- name    : Formalism.L2.G.exists_sq_eq_intCast_of_not_dvd_of_ne_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:17.217199+00:00
-- url     : https://prove2.me/theorems/c86ebb52-cd2c-4d20-b402-ea89d6de5bee
-- title:
--   G: exists sq eq int Cast of not dvd of ne two
-- statement:
--   The G construction uses the exists sq eq int Cast of not dvd of ne two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L451-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L451-L469

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

theorem Formalism.L2.G.exists_sq_eq_intCast_of_not_dvd_of_ne_two (hp2 : p ≠ 2) (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : ∃ y : W2 p n, y ^ 2 = (z : W2 p n) := by sorry
