-- Prove2me | Theorems.Thm_CollatNet_Termination_lemma_5_1
-- name    : CollatNet.Termination.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:12.4896+00:00
-- url     : https://prove2.me/theorems/f111d4b4-1095-4eff-9eac-638f3d21a308
-- title:
--   Lemma 5.1, pp. 29–30 (PDF 30–31) — at π = π̂ = 1, p^(2)_ij ≥ q^(2)_ij at the largest or at the smallest second-round payments
-- statement:
--   Let the network satisfy the standing assumptions, with constant collateral price $\pi = \hat\pi = 1$, and let $p^{(1)}$ be first-round clearing payments (common to both models). Let $p^{(2)}$ be round-2 clearing payments under full termination and $q^{(2)}$ round-2 clearing payments under selective termination, and suppose that either both are the largest such payments, or both are the smallest. Then
--   $$
--   p^{(2)}_{ij} \ge q^{(2)}_{ij} \qquad \text{for all } i, j \in \mathcal N .
--   $$
--
--   Full termination creates more obligations, and at the extremal solutions it also produces more payments in Round 2; this is the first step in comparing payment shortfalls.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), pp. 29–30 (PDF 30–31), Lemma 5.1, (36); proof in A.9, p. 44 (PDF 45)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Lemma 5.1, pp. 29–30: at `π = π̂ = 1`, `p^(2)_ij ≥ q^(2)_ij` for all `i, j`, taking the largest
round-2 clearing payments under both models, or the smallest under both. -/
theorem lemma_5_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p1 : ι → ι → ℝ) (hp1 : Clears1 X p1) (x y : ι → ι → ℝ)
    (hext : (IsGreatest (round2FT X p1) x ∧ IsGreatest (round2ST X p1) y) ∨
      (IsLeast (round2FT X p1) x ∧ IsLeast (round2ST X p1) y)) :
    ∀ i j, y i j ≤ x i j := by sorry

end CollatNet.Termination
