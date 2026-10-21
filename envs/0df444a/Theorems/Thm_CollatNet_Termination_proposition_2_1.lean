-- Prove2me | Theorems.Thm_CollatNet_Termination_proposition_2_1
-- name    : CollatNet.Termination.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:59.441722+00:00
-- url     : https://prove2.me/theorems/640aa8a8-a970-4798-b276-b5ff58652f22
-- title:
--   Proposition 2.1, p. 13 (PDF 14) — two-round clearing payments exist and their node totals satisfy (15)
-- statement:
--   Let $(\bar p,c,m,v)$ be a collateralized network satisfying the standing assumptions, with constant collateral price $1$. Proposition 2.1 concerns the two-round freed-collateral model of §2.3, without accelerated derivative obligations. There exist nonnegative matrices $p^{(1)}$ and $p^{(2)}$ satisfying the first-round clearing equations (6)–(9) and the second-round equations (11)–(14). In the latter, $\bar p^{(2)}_{ij}=\bar p_{ij}-p^{(1)}_{ij}$, $r_i$ is the collateral returned after Round 1, and $a^{(2)}_{ij}=\bar p^{(2)}_{ij}/\sum_k\bar p^{(2)}_{ik}$, taken as $0$ when the denominator is $0$. Moreover, for every node $i$, the total paid over both rounds obeys (15):
--   $$
--   \sum_j p^{(1)}_{ij}+\sum_j p^{(2)}_{ij}=\min\!\left\{\bar p_i,\; c_i+\sum_k(p^{(1)}_{ki}+p^{(2)}_{ki})+\sum_k m_{ik}\right\}.
--   $$
--   This result supplies the first-round clearing payments used by the termination model and records the paper's total-payment identity.
--
--   **Formalization Note.** The later full-termination rounds are separate from the §2.3 Round 2 stated here. Sums over all nodes equal the paper's sums over $k\ne i$ under the standing zero-diagonal assumptions. The theorem includes the entire claim of Proposition 2.1.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), p. 13 (PDF 14), Proposition 2.1, (6)–(9), (11)–(15)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

/-- Proposition 2.1, p. 13: first- and second-round clearing payments satisfying (6)–(9)
and (11)–(14) exist, and their node totals obey (15). -/
theorem proposition_2_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) :
    ∃ p1 p2 : ι → ι → ℝ, Clears1 X p1 ∧ ClearsBase2 X p1 p2 ∧
      ∀ i, (∑ j, p1 i j) + (∑ j, p2 i j) =
        min (oblTot X i)
          (X.c i + (∑ k, (p1 k i + p2 k i)) + (∑ k, X.m i k)) := by sorry

end CollatNet.Termination
