-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_3_4
-- name    : ChengCapClustering.Soft.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:13.414616+00:00
-- url     : https://prove2.me/theorems/1c8f1ff2-8374-4cc1-ab9f-a7bf31851bda
-- title:
--   Lemma 3.4 — triangle bound: every block is $(3^{z-1},(3/2)^{z-1})$-movable
-- statement:
--   For $z\ge1$, every block of every block partition is $(3^{z-1},(3/2)^{z-1})$-movable: for all slots $y_1,\dots,y_w\in F$ some bijection $\varphi$ from the block to $\{1,\dots,w\}$ satisfies $\sum_{p}\mathrm{dist}(p,y_{\varphi(p)})^z\le 3^{z-1}A_i+(3/2)^{z-1}\sum_p\mathrm{dist}(a_i,y_{\varphi(p)})^z$.
--
--   Differences from the source:
--   - generalization: every block of every block partition (size ≤ U, representative in F, part of a partition with m ≤ 2k − 1 blocks) → every finite index set Q in any metric space, with any point map, any representative a and any slot set F; reason: the triangle-inequality proof uses neither block-size restrictions nor finite F nor joint doubling; every source block is included
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 3.4, printed p. 8 / PDF p. 10

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering

universe u v

namespace ChengCapClustering.Soft

/-- Lemma 3.4 (Triangle bound), printed p. 8 / PDF p. 10: every block, with any representative and
any slot locations, is `(3^{z−1}, (3/2)^{z−1})`-movable. -/
theorem lemma_3_4 (V : Type u) [MetricSpace V] (z : ℝ) (hz : 1 ≤ z) (F : Set V) {ι : Type v}
    (Q : Finset ι) (pt : ι → V) (a : V) :
    IsMovable z ((3 : ℝ) ^ (z - 1)) (((3 : ℝ) / 2) ^ (z - 1)) F Q pt a := by sorry

end ChengCapClustering.Soft
