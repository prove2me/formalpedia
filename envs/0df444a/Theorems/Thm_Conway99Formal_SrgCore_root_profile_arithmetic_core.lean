-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_root_profile_arithmetic_core
-- name    : Conway99Formal.SrgCore.root_profile_arithmetic_core
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:22:00.181029+00:00
-- url     : https://prove2.me/theorems/603013e1-50e7-4c12-be7f-65c9ae422371
-- title:
--   Divisibility conditions restrict the root parameter
-- statement:
--   For a natural number m at least one, suppose even m implies 2^m divides 4m−4 and odd m implies 2^(m−1) divides 4m−4. Then m belongs to the listed set.
--
--   $$m\ge1,\quad (2\mid m\Rightarrow 2^m\mid4m-4),\quad (2\nmid m\Rightarrow 2^{m-1}\mid4m-4)\Longrightarrow m\in\{1,2,3,5\}$$
--
--   Role: The parity cases are separate conditional hypotheses, not unconditional divisibility premises.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L182-L209; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L182-L209.

import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.SrgCore.root_profile_arithmetic_core (m : ℕ) (hm : 1 ≤ m)
    (heven : Even m → 2 ^ m ∣ 4 * m - 4)
    (hodd : Odd m → 2 ^ (m - 1) ∣ 4 * m - 4) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 5 := by sorry
