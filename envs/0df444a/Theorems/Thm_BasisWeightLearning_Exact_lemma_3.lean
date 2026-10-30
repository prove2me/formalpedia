-- Prove2me | Theorems.Thm_BasisWeightLearning_Exact_lemma_3
-- name    : BasisWeightLearning.Exact.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:22:09.409865+00:00
-- url     : https://prove2.me/theorems/fabab9fa-d536-4a63-9c5a-133cbb5d7da6
-- title:
--   Lemma 3 — Preservation of the positive-normal frontier
-- statement:
--   Let $\Phi=(\phi_0,\ldots,\phi_d)$ be a nonnegative basis family in $L^2([0,1])$. Let $W\subseteq\mathbb R^{d+1}$ be any finite set and define $U=\{\Phi w:w\in W\}$. Then every $u\in\operatorname{PNEP}(U)$ equals $\Phi w$ for some $w\in\operatorname{PNEP}(W)$, and
--   $$\operatorname{PNEP}(U)=\operatorname{PNEP}(\{\Phi w:w\in\operatorname{PNEP}(W)\}).$$
--   Vector normals have nonnegative coordinates summing to one; function normals are all nonnegative L2 densities of integral one. Both operations use strict exposure against every distinct competitor. The outer function frontier permits coefficient vertices that become redundant after evaluation. Empty and singleton sets are included.
--
--   Differences from the source:
--   - encoding: a nonnegative basis family in L2 with unique coordinates → nonnegative square-integrable representatives with linear independence of their L2 classes; reason: this makes the source Hilbert-space basis convention explicit without requiring continuity or strict positivity
--   - encoding: vectors in R^(d+1) and their simplex normals → real functions on Fin (d+1) and finite sums; reason: the index set has precisely the source zero-based d+1 coordinates
--   - encoding: functions on [0,1] and Lebesgue integration → functions on the interval subtype with the pullback of real Lebesgue measure; reason: equality is exactly equality on the source domain and every admissible L2 density remains available
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 17 (printed p. 17), Lemma 3; proof PDF p. 52 (EC p. 8).

import Definitions.Def_BasisWeightLearning_Exact_Basis
import Definitions.Def_BasisWeightLearning_Exact_VectorFrontier

namespace BasisWeightLearning.Exact
theorem lemma_3 (d : ℕ) (Φ : BasisFamily d)
    (W : Set (Fin (d + 1) → ℝ)) (hW : W.Finite) :
    (∀ u ∈ functionFrontier (Φ.evaluate '' W),
      ∃ w ∈ vectorFrontier W, Φ.evaluate w = u) ∧
    functionFrontier (Φ.evaluate '' W) =
      functionFrontier (Φ.evaluate '' vectorFrontier W) := by sorry
end BasisWeightLearning.Exact
