-- Prove2me | Theorems.Thm_AlmostMMS_Supplement_theorem_2_1
-- name    : AlmostMMS.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:29:05.192817+00:00
-- url     : https://prove2.me/theorems/82c2f267-343e-4329-8af2-f4a43c694eae
-- title:
--   Theorem 2.1 — MMS($d$) allocations exist for $d\ge n+46(1+\log n)^2$
-- statement:
--   Consider a fair allocation instance with a finite set of items $M$ and $n\ge1$ agents $N$ whose valuations $v_i$ are additive and nonnegative. If
--   $$
--   d\ \ge\ n+46\,(1+\log_2 n)^2,
--   $$
--   then the instance has an MMS($d$) allocation: a partition $(A_1,\dots,A_n)$ of $M$ with $v_i(A_i)\ge\mathrm{MMS}(M,v_i,d)$ for every agent $i$.
--
--   This is the formal version of Theorem 1.2 ($d=n+O(\log^2 n)$ suffices for 1-out-of-$d$ MMS), improving the earlier $d=4\lceil n/3\rceil$ and $d=n+O(\sqrt n\log n)$ to a polylogarithmic number of extra bundles. The valuations are arbitrary; the ordering and normalization of Assumption 1 are made without loss of generality inside the proof.
--
--   Differences from the source:
--   - encoding: n agents and log n → hypothesis 1 ≤ n; reason: log n is undefined at n = 0, and an instance with agents N has n ≥ 1
--   - encoding: log → Real.logb 2; reason: the paper's log is binary (p.19 rewrites log(2n²) as 2(1 + log n) − 1)
--   - encoding: MMS(M, v_i, d) and partitions of M → the published mms over labelled, possibly empty d-partitions and a total map from items to agents; reason: the same objects
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 2.1, p.10 (= Theorem 1.2, p.2)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_AlmostMMS_Supplement_AdmitsMMSdAlloc

namespace AlmostMMS.Supplement

open Finset

/-- **Theorem 2.1 (Theorem 1.2 restated), p.10.** Feige, Grinberg, *Almost-MMS allocations with small
agent redundancy*, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…): in every fair
allocation instance with items `M` and `n` additive agents there is an MMS(`d`) allocation whenever
`d ≥ n + 46(1 + log n)²`.

**Formalization Note.** `log` is base `2` (p.19 rewrites `log(2n²)` as `2(1 + log n) - 1`). The
valuations are arbitrary additive nonnegative set functions (`LittleCharity.MMS.IsAdditive`);
Assumption 1 (ordered values, MMS bundles of value 1) is a reduction made inside the proof, not a
hypothesis. `1 ≤ n`: the instance has agents `N = [n]`. -/
theorem theorem_2_1 {n m d : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (hn : 1 ≤ n)
    (hd : (n : ℝ) + 46 * (1 + Real.logb 2 (n : ℝ)) ^ 2 ≤ (d : ℝ)) :
    AdmitsMMSdAlloc v d := by sorry

end AlmostMMS.Supplement
