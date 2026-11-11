-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_proposition_4_2
-- name    : ExactDFTRefine.Main.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:02:09.945836+00:00
-- url     : https://prove2.me/theorems/b0e56967-9dfe-4b33-88ec-bc8574601931
-- title:
--   Proposition 4.2 — for v = 11640, J = 20^v, B = 21^v: M_t(P′) < M_t(T′) and every block rank is below every target rank
-- statement:
--   Let $v = 11640$, $J = 20^{v}$, $B = 21^{v}$ and $t = 1 - C$ with $C = 60403319/20000000000$, and let $P'$, $T'$ be the completed and split $v$-fold tensor unit of the Table 1 multisets (as in Lemma 4.1). Then
--   $$M_t(P') < M_t(T'),$$
--   and every charged-block rank is smaller than every target rank: $p < q$ for all $p \in P'$ and $q \in T'$.
--   These are the two hypotheses that Sussman's mixed-target recursion needs from the finite unit.
--
--   Differences from the source:
--   - reading: Proposition 4.2 names only v = 11640 → J = 20^11640, B = 21^11640 and t = 1 − C fixed in the statement; reason: the paragraph before the proposition sets J = 20^v and B = 21^v and works at t = 1 − C
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 5, Proposition 4.2

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Proposition 4.2**, p. 5. For `v = 11640`, `J = 20^v`, `B = 21^v` and `t = 1 - C`, the
completed and split tensor unit has `M_t(P′) < M_t(T′)`, and every charged-block rank is smaller
than every target rank. -/
theorem proposition_4_2 :
    moment tpar (Pprime blocksP targetsT 11640 (20 ^ 11640) (21 ^ 11640)) <
      moment tpar (Tprime targetsT 11640 (21 ^ 11640)) ∧
    ∀ p ∈ Pprime blocksP targetsT 11640 (20 ^ 11640) (21 ^ 11640),
      ∀ q ∈ Tprime targetsT 11640 (21 ^ 11640), p < q := by sorry

end ExactDFTRefine.Main
