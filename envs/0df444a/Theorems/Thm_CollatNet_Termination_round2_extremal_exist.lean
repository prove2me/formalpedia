-- Prove2me | Theorems.Thm_CollatNet_Termination_round2_extremal_exist
-- name    : CollatNet.Termination.round2_extremal_exist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:03.30042+00:00
-- url     : https://prove2.me/theorems/b9f9fa9e-ef7a-4d0a-b6bc-d8a5a5f8b6db
-- title:
--   Proof of Lemma 5.1, p. 44 (PDF 45) — largest and smallest round-2 clearing payments exist under FT and ST
-- statement:
--   Let the network satisfy the standing assumptions, with collateral price $1$, and let $p^{(1)}$ be first-round clearing payments. Consider the set of round-2 clearing payments under full termination, i.e. matrices $x \ge 0$ with
--   $$
--   x_{ij} = \bar p^{(2)}_{ij} \wedge \big[\Delta^{(2)}_{ij} + a^{(2)}_{ij}\big(c^{(2)}_i + r^{(2)}_i + \textstyle\sum_k x_{ki}\big)\big],
--   $$
--   and the analogous set under selective termination, with $\bar q^{(2)}$ in place of $\bar p^{(2)}$. Each of the two sets has a largest and a smallest element in the componentwise order.
--
--   The comparison of Lemma 5.1 and Proposition 5.2 is made at these extremal solutions; this result guarantees that they exist.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), proof of Lemma 5.1 (A.9), p. 44 (PDF 45); existence part of Proposition 5.1, p. 28 (PDF 29)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Proof of Lemma 5.1, p. 44 (and Proposition 5.1, p. 28): given clearing first-round payments,
the round-2 clearing payments of the full-termination model and of the selective-termination model
each have a largest and a smallest element. -/
theorem round2_extremal_exist {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p1 : ι → ι → ℝ) (hp1 : Clears1 X p1) :
    (∃ x, IsGreatest (round2FT X p1) x) ∧ (∃ x, IsLeast (round2FT X p1) x) ∧
      (∃ y, IsGreatest (round2ST X p1) y) ∧ (∃ y, IsLeast (round2ST X p1) y) := by sorry

end CollatNet.Termination
