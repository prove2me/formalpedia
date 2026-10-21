-- Prove2me | Theorems.Thm_CollatNet_Termination_round2_dominance
-- name    : CollatNet.Termination.round2_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:58.576892+00:00
-- url     : https://prove2.me/theorems/bba190b9-7086-4138-94f8-464f6ae50ec4
-- title:
--   Proof of Lemma 5.1, p. 44 (PDF 45) — p̄^(2) ≥ q̄^(2) and a^(2) ≥ â^(2)
-- statement:
--   Let the network satisfy the standing assumptions, with collateral price $1$, and let $p^{(1)}$ be first-round clearing payments. The round-2 obligations under full termination,
--   $$
--   \bar p^{(2)}_{ij} = \begin{cases} v_{ij} + \bar p_{ij} - p^{(1)}_{ij}, & i \text{ or } j \in D^{(1)},\\ 0, & \text{otherwise}, \end{cases}
--   $$
--   and under selective termination,
--   $$
--   \bar q^{(2)}_{ij} = \begin{cases} v_{ij} + \bar p_{ij} - p^{(1)}_{ij}, & i \in D^{(1)},\\ 0, & \text{otherwise}, \end{cases}
--   $$
--   satisfy $\bar p^{(2)}_{ij} \ge \bar q^{(2)}_{ij}$ for all $i, j$. Moreover the round-2 proportions $a^{(2)}_{ij} = \bar p^{(2)}_{ij} / \sum_k \bar p^{(2)}_{ik}$ and $\hat a^{(2)}_{ij} = \bar q^{(2)}_{ij} / \sum_k \bar q^{(2)}_{ik}$ (each $0$ when its denominator vanishes) satisfy $a^{(2)}_{ij} \ge \hat a^{(2)}_{ij}$ for all $i, j$.
--
--   These are the two monotone comparisons of parameters from which Lemma 5.1 follows.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), proof of Lemma 5.1 (A.9), p. 44 (PDF 45), (63)–(66)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Proof of Lemma 5.1, p. 44: the full-termination round-2 obligations (63) dominate the
selective-termination ones (64), `p̄^(2) ≥ q̄^(2)`, and so do the proportions, `a^(2) ≥ â^(2)`
((65), (66)). -/
theorem round2_dominance {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p1 : ι → ι → ℝ) (hp1 : Clears1 X p1) :
    (∀ i j, (initST X p1).obl i j ≤ (initFT X p1).obl i j) ∧
      (∀ i j, ratio (initST X p1).obl i j ≤ ratio (initFT X p1).obl i j) := by sorry

end CollatNet.Termination
