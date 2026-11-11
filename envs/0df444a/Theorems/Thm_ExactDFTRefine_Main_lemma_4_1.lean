-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_lemma_4_1
-- name    : ExactDFTRefine.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:49.794038+00:00
-- url     : https://prove2.me/theorems/9ed92e5c-ff5b-4248-b39e-5f6bc60bb8be
-- title:
--   Lemma 4.1 — completion and splitting: M_t(P′) ≤ P_t^v + 2J^{t−1}P_1^v + 2|T|^v B J^{t−1} and M_t(T′) ≥ T_t^v
-- statement:
--   Let $P$, $T$ be the Table 1 multisets, $v \ge 1$, and $J < B$ positive integers. In the $v$-fold tensor unit, complete every target $K \in T^{\otimes v}$ with $K < B$ to rank $B$ by adding a charged block of rank $B - K$ (targets with $K \ge B$ are unchanged), then split every charged block of rank $R > J$ into $\lfloor R/J \rfloor$ blocks of rank $J$ and one remainder block of rank $R \bmod J$ if that is nonzero. Let $P'$ and $T'$ be the resulting charged-block and target multisets. Then for every $0 \le t \le 1$,
--   $$M_t(P') \le P_t^v + 2J^{t-1}P_1^v + 2|T|^v B J^{t-1}, \qquad M_t(T') \ge T_t^v. \tag{13}$$
--   Here $J^{t-1}$ is a real power with nonpositive exponent. Lemma 4.1 reduces the moment comparison of the separated tensor unit to the three-term inequality (14).
--
--   Differences from the source:
--   - reading: each charged block of rank R > J is split into blocks of rank J and one remainder block, if needed → ⌊R/J⌋ blocks of rank J and one block of rank R mod J when R mod J ≠ 0; the completion blocks are split too; reason: the proof of Lemma 4.1 bounds the pieces by ⌊R/J⌋J^t + (R mod J)^t and splits the completion blocks
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 5, Lemma 4.1 (Eq. (13))

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Lemma 4.1 (Completion and splitting)**, p. 5. For `0 ≤ t ≤ 1`, `v ≥ 1` and positive
integers `J < B`, the completed and split `v`-fold tensor unit of the Table 1 multisets satisfies
`M_t(P′) ≤ P_t^v + 2 J^{t-1} P_1^v + 2 |T|^v B J^{t-1}` and `M_t(T′) ≥ T_t^v` (13). -/
theorem lemma_4_1 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (v : ℕ) (hv : 1 ≤ v) (J B : ℕ)
    (hJ : 0 < J) (hJB : J < B) :
    moment t (Pprime blocksP targetsT v J B) ≤
      moment t blocksP ^ v + 2 * (J : ℝ) ^ (t - 1) * moment 1 blocksP ^ v +
        2 * (Multiset.card targetsT : ℝ) ^ v * (B : ℝ) * (J : ℝ) ^ (t - 1) ∧
    moment t (Tprime targetsT v B) ≥ moment t targetsT ^ v := by sorry

end ExactDFTRefine.Main
