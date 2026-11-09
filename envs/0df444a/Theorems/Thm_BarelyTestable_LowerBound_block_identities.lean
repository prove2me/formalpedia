-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_block_identities
-- name    : BarelyTestable.LowerBound.block_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:23:41.788841+00:00
-- url     : https://prove2.me/theorems/962a2c9c-49eb-4bf5-b12a-bda551569edf
-- title:
--   Claim 3.16 — all block-count and squared-count identities
-- statement:
--   Fix one block of $m\ge1$ coordinates, its prescribed parity $\pi$, a target subset $U$ and $w=|U|$. Let $s_j$ sum the ordered operation counts over the parity class, and $t_j$ sum their squares. All six identities hold:
--
--   $$s_1=s_3=mw,\qquad s_2=m(m-w),$$
--   $$ (t_1,t_2,t_3)=\begin{cases}(m^2w^2,m^2(m-w)^2,w(m+2w-2)),&w\equiv\pi\pmod2,\\(m^2w,m^2(m-w),mw^2),&w\not\equiv\pi\pmod2.\end{cases}$$
--
--   Counts include every ordered pair, even when an operation does not use the second coordinate. These identities apply to each block separately.
--
--   Differences from the source:
--   - encoding: an indexed block A_i and operation indices 1,2,3 → an anonymous copy Fin m of any block, with indices 0,1,2; reason: every block has the same size and operations; both parity cases and all six equalities are retained
--   - generalization: Claim 3.16 for a block A_i, i ∈ [m], under the standing assumption of §3 (p.11) that m is a large enough integer → every m ≥ 1; reason: the source proof uses no lower bound on m, and the Lean statement specializes to every large m
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Claim 3.16, p. 22 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Claim 3.16, p.22: three sums and all six parity cases for the squared sums. -/
theorem block_identities {m : ℕ} (hm : 1 ≤ m) (π : Bool) (U : Cube (Fin m)) :
    let w := U.card
    let same := decide (w % 2 = 1) = π
    blockS 0 π U = m * w ∧
    blockT 0 π U = (if same then m^2 * w^2 else m^2 * w) ∧
    blockS 1 π U = m * (m - w) ∧
    blockT 1 π U = (if same then m^2 * (m-w)^2 else m^2 * (m-w)) ∧
    blockS 2 π U = m * w ∧
    blockT 2 π U = (if same then w * (m + 2*w - 2) else m * w^2) := by sorry

end BarelyTestable.LowerBound
