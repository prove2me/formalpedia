-- Prove2me | Theorems.Thm_CollatNet_Termination_proposition_5_2_i
-- name    : CollatNet.Termination.proposition_5_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:00.864044+00:00
-- url     : https://prove2.me/theorems/0e9aa236-45c4-473b-97f6-db83e2859623
-- title:
--   Proposition 5.2 (i), p. 30 (PDF 31) — constant collateral price, (37) or (38), leverage condition (40) ⇒ L^f ≤ L^s
-- statement:
--   Let $(\bar p, c, m, v)$ be a collateralized network satisfying the standing assumptions (nonnegative data, zero diagonals, netted obligations and derivatives values), and let the collateral price be constant, $\pi = \hat\pi = 1$ (case (i)). Let $p^{(1)}, \dots, p^{(R)}$ be clearing payments of the full-termination (FT) model, and let the selective-termination (ST) model use the same first-round payments, $q^{(1)} = p^{(1)}$, and round-2 clearing payments $q^{(2)}$. Assume one of
--
--   1. (37): $p^{(2)}$ and $q^{(2)}$ are the largest second-round clearing payments of their models;
--   2. (38): $p^{(2)}$ and $q^{(2)}$ are the smallest second-round clearing payments of their models.
--
--   Let $D^f = \bigcup_{l} D^{(l)}$ be the FT default set, $D^{(1)}$ the first-round (and ST) default set, $v_i = \sum_j v_{ij}$, and $e_i = c_i + r_i + \sum_k p^{(1)}_{ki} - \sum_k \bar p_{ik}$ the net worth at the end of Round 1. Under the aggregate derivatives leverage condition
--   $$
--   \sum_{i \in D^f - D^{(1)}} v_i \;\le\; \sum_{i \in D^f - D^{(1)}} e_i ,
--   $$
--   full termination reduces payment shortfalls:
--   $$
--   L^f = \sum_{i \in D^f} \big(v_i + \bar p_i - p_i\big) \;\le\; L^s = \sum_{i \in D^{(1)}} \big(v_i + \bar p_i - q_i\big),
--   $$
--   with $p_i = \sum_{l} \sum_j p^{(l)}_{ij}$ and $q_i = \sum_j \big(p^{(1)}_{ij} + q^{(2)}_{ij}\big)$.
--
--   Accelerating all derivative contracts of a defaulted bank creates new obligations and possibly new defaults; the proposition says that, with liquid collateral and derivatives liabilities bounded by equity in aggregate, the extra payments it releases outweigh the extra shortfall.
--
--   **Formalization Note.** Only case (i) is posed; the paper's case (ii) (illiquid collateral, no excess collateral) is false as printed: a single surviving node $i$ with $c_i = \bar p_{ij} = m_{ij} = v_{ij} = 10$ whose debtor $j$ owes $20$ elsewhere sells its returned collateral at a depressed price, giving $L^f = 20(1 - e^{-10\alpha}) > 10 = L^s$ for $\alpha > \ln 2/10$. The cash recursion of the Model is the disclosed repair of p. 24 (unsold returned collateral is carried as cash; seized collateral is not paid out of cash); with the literal recursion the statement fails on a four-node network. Clearing payments are nonnegative, the number of rounds is $R = \max(2, N)$, "largest/smallest" is in the componentwise order on the round-2 clearing sets, and FT rounds $3, \dots, R$ may be any clearing payments.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), p. 30 (PDF 31), Proposition 5.2 (i), with (34), (35) p. 28 (PDF 29), (37)–(40) p. 30 (PDF 31)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

open Finset

/-- Proposition 5.2 (i), p. 30: with constant collateral price `π = π̂ = 1`, common Round-1 payments,
both models at their largest (37) or both at their smallest (38) round-2 clearing payments, and the
aggregate derivatives leverage condition (40), full termination leaves no larger payment shortfall
than selective termination: `L^f ≤ L^s`. -/
theorem proposition_5_2_i {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (q2 : ι → ι → ℝ) (hp : ClearsFT X p)
    (hext : (IsGreatest (round2FT X (p 1)) (p 2) ∧ IsGreatest (round2ST X (p 1)) q2) ∨
      (IsLeast (round2FT X (p 1)) (p 2) ∧ IsLeast (round2ST X (p 1)) q2))
    (h40 : ∑ i ∈ Df X p \ D1 X (p 1), vTot X i ≤
      ∑ i ∈ Df X p \ D1 X (p 1), netWorth X (p 1) i) :
    shortfallFT X p ≤ shortfallST X (p 1) q2 := by sorry

end CollatNet.Termination
