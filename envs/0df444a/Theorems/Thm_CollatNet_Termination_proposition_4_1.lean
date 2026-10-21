-- Prove2me | Theorems.Thm_CollatNet_Termination_proposition_4_1
-- name    : CollatNet.Termination.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:07.778285+00:00
-- url     : https://prove2.me/theorems/874ecee8-3871-4713-ac29-2f6f53da1af8
-- title:
--   Proposition 4.1, p. 26 (PDF 27), at π ≡ 1 — clearing payments exist in every round m = 1, …, N of full termination
-- statement:
--   Let $(\bar p,c,m,v)$ be a collateralized network satisfying the standing assumptions, with the collateral price fixed at $1$. Then there exists a sequence of nonnegative clearing payment matrices $p^{(1)},\ldots,p^{(R)}$, where $R=\max(2,N)$ and $N$ is the number of nodes, such that Round 1 satisfies (6)–(9) and every later round satisfies the full-termination clearing equation (30) in the state determined by earlier rounds:
--   $$
--   p^{(m)}_{ij}=\bar p^{(m)}_{ij}\wedge\big[\Delta^{(m)}_{ij}+a^{(m)}_{ij}A^{(m)}_i\big],\qquad 2\le m\le R.
--   $$
--   This is Proposition 4.1's existence conclusion for the liquid-collateral case.
--
--   **Formalization Note.** Every collateral price is $1$, so the price component of the paper's conclusion is fixed. The convention $R=\max(2,N)$ gives a formally defined Round 2 even for a network with at most one node; zero diagonals make its obligations vanish.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), p. 26 (PDF 27), Proposition 4.1; proof in A.8, p. 43 (PDF 44)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Proposition 4.1, p. 26, at `π ≡ 1`: clearing payments exist in every round `m = 1, …, N`. -/
theorem proposition_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) :
    ∃ p : ℕ → ι → ι → ℝ, ClearsFT X p := by sorry

end CollatNet.Termination
