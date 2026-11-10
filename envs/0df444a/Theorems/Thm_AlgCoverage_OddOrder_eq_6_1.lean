-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_6_1
-- name    : AlgCoverage.OddOrder.eq_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:23.785509+00:00
-- url     : https://prove2.me/theorems/b7e954ea-48e6-49ee-8662-94f06a0c6cf0
-- title:
--   §6, Eq. (6.1) — every odd-order group has a $G$-normal elementary-abelian chief series (via Feit–Thompson), and every such series has $J,D\le\log_3N$
-- statement:
--   Let $G$ be a finite group of odd order $N$. Then $G$ has a **chief series** of the form (6.1),
--   $$1=A_0\triangleleft A_1\triangleleft\cdots\triangleleft A_J=G,\qquad A_r\triangleleft G,\qquad A_r/A_{r-1}\cong\mathbb F_{p_r}^{d_r},\ p_r\text{ odd prime},$$
--   that is, a $G$-normal elementary-abelian series whose layers $A_r/A_{r-1}$ are minimal normal subgroups of $G/A_{r-1}$ (no normal subgroup of $G$ lies strictly between $A_{r-1}$ and $A_r$). Moreover every $G$-normal elementary-abelian series (6.1) of $G$ satisfies
--   $$J\le\log_3N,\qquad D:=\max_r d_r\le\log_3N.$$
--   The existence uses the odd-order theorem of Feit and Thompson (solvability of groups of odd order); the bound holds because every layer has order at least $3$.
--
--   Differences from the source:
--   - reading: A_r/A_{r−1} ≅ F_{p_r}^{d_r} with ◁ between consecutive terms → every layer nontrivial, d_r ≥ 1; reason: J ≤ log₃ N is false if trivial layers were allowed, and chief factors are nontrivial
--   - encoding: A_r/A_{r−1} ≅ F_{p_r}^{d_r} → a MulEquiv between ↥(A (r+1)) ⧸ (A r).subgroupOf (A (r+1)) and Multiplicative (Fin (d r) → ZMod (p r)), 0-based layers; reason: the additive group F_p^d written multiplicatively; the paper's layer r is Lean's layer r − 1
--   - encoding: 'a chief series of this form' → a series of type NormalEASeries G such that no normal subgroup of G lies strictly between consecutive terms; reason: definition of a chief series
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 21 (PDF 22), §6, Eq. (6.1); p. 7 (PDF 8), §2.3

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Series

namespace AlgCoverage.OddOrder

/-- §6, Eq. (6.1), Lin, printed p. 21 / PDF 22. Every finite group `G` of odd order `N` admits a
`G`-normal elementary-abelian series (6.1) with odd primes (via the odd-order theorem [FT63]), and every
such series has `J ≤ log₃ N` and `D = max_r d_r ≤ log₃ N`. The series supplied by the odd-order theorem is a
chief series: no normal subgroup of `G` lies strictly between consecutive terms. -/
theorem eq_6_1 (G : Type*) [Group G] [Fintype G] (hodd : Odd (Fintype.card G)) :
    (∃ s : NormalEASeries G, ∀ r, r < s.J → ∀ M : Subgroup G, M.Normal →
      s.A r ≤ M → M ≤ s.A (r + 1) → M = s.A r ∨ M = s.A (r + 1)) ∧
    ∀ s : NormalEASeries G,
      (s.J : ℝ) ≤ Real.logb 3 (Fintype.card G) ∧ (s.D : ℝ) ≤ Real.logb 3 (Fintype.card G) := by sorry

end AlgCoverage.OddOrder
