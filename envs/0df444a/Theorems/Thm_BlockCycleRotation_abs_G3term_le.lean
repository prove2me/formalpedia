-- Prove2me | Theorems.Thm_BlockCycleRotation_abs_G3term_le
-- name    : BlockCycleRotation.abs_G3term_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:04.098366+00:00
-- url     : https://prove2.me/theorems/79f057bd-3384-4087-be7f-dbbc762995da
-- title:
--   Lemma 18 at a single coprime pair
-- statement:
--   For a bulk pair $a > a' \ge 1$ with $\gcd(a,a')=1$ and $d\,a(a+a') \le m$,
--   $$|G_3(m,d,a,a')| \le \bigl(|A(m,d,a)| + |B(a,a')|\,(Y-1)\bigr)\,(1+\log a).$$
--
--   The factor $1+\log a$ is the character-sum loss: bounding the deviation of a linear sum over an arithmetic progression modulo $a$ by orthogonality produces $\sum_{m \ne 0} 1/\min(m, a-m) \ll \log a$. This is the per-pair form of Lemma 18.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L292-L308

import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.abs_G3term_le {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hgcd : Nat.gcd a a' = 1) (hbulk : d * a * (a + a') ≤ m) :
    |G3term m d a a'|
      ≤ (|aCoeff m d a| + |bCoeff a a'| * ((gtBound m d a a' - 1 : ℕ) : ℝ))
          * (1 + Real.log a) := by sorry
