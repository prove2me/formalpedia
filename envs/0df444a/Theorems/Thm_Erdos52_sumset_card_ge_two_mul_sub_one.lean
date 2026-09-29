-- Prove2me | Theorems.Thm_Erdos52_sumset_card_ge_two_mul_sub_one
-- name    : Erdos52.sumset_card_ge_two_mul_sub_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T16:21:01.500561+00:00
-- url     : https://prove2.me/theorems/622be207-8b45-44eb-8be0-def178186340
-- title:
--   Trivial bound $|A+A|\ge 2|A|-1$
-- statement:
--   Let $A$ be a nonempty finite set of integers and $A+A=\{a+b : a,b\in A\}$ its sumset. Then
--
--   $$|A+A|\ \ge\ 2|A|-1.$$
--
--   Equality holds exactly for arithmetic progressions, which shows that the sumset alone can be as small as linear in $|A|$; the sum–product problem asks how small $|A+A|$ and $|AA|$ can be simultaneously.
-- source:
--   https://www.erdosproblems.com/52; see the milestone description for the literature reference

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem sumset_card_ge_two_mul_sub_one (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by sorry
end Erdos52
