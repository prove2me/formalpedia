-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_eq_2
-- name    : ExactDFTRefine.Main.eq_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:48.027278+00:00
-- url     : https://prove2.me/theorems/c5c877d4-5b65-4086-bc5f-896bffc831bb
-- title:
--   §2, Eq. (2) — P_1 = 239134, T_1 = 239886, |T| = 10928 for the Table 1 multisets
-- statement:
--   For the charged-block multiset $P$ and the target multiset $T$ of Table 1, with $M_t(A) = \sum_{r\in A} r^t$ counting multiplicity,
--   $$P_1 = M_1(P) = 239134, \qquad T_1 = M_1(T) = 239886, \qquad |T| = 10928.$$
--   This is the checksum of Table 1: the first moments are the total ranks and $|T|$ is the number of target jobs, counted with multiplicity.
--
--   Differences from the source:
--   - encoding: P_1 = Σ_{r∈P} r → moment 1 blocksP, the real power r^(1:ℝ); reason: r^1 = r; same value
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 3, §2, Eq. (2)

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **§2, Eq. (2)**, p. 3. For the Table 1 multisets: `P_1 = 239134`, `T_1 = 239886`,
`|T| = 10928`. -/
theorem eq_2 :
    moment 1 blocksP = 239134 ∧ moment 1 targetsT = 239886 ∧
    Multiset.card targetsT = 10928 := by sorry

end ExactDFTRefine.Main
