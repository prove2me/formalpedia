-- Prove2me | Theorems.Thm_EssCheck_Accuracy_revenues_foc
-- name    : EssCheck.Accuracy.revenues_foc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:05.586258+00:00
-- url     : https://prove2.me/theorems/2be4d7a8-5f96-428a-a459-b5fae8e4f6bf
-- title:
--   §4, equation (5) — licensing revenues and private investment wedge
-- statement:
--   Fix accuracy $\beta\in[0,1]$ and an interior expected effort $\hat x$. In a hybrid state $i$, the upstream firm's revenue after success is $\bar\alpha v_i-\tilde z_i l_i$, and after failure with certification it is $l_i$. In a pooling state, both revenues are $\bar\alpha v_i$. Averaging success and failure revenues over their respective value distributions gives
--   $$\pi^H-\pi^L=\sum_{i\in H}p_i^H(\bar\alpha v_i-\tilde z_i l_i)+\sum_{i\in P}p_i^H\bar\alpha v_i-(1-\beta)\left(\sum_{i\in H}p_i^0l_i+\sum_{i\in P}p_i^0\bar\alpha v_i\right).$$
--   This is the left-hand side of the upstream firm's research first-order condition (5).
--
--   **Formalization Note** The revenue after failure includes the certification probability $1-\beta$; an uncertified patent produces zero upstream revenue.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), p. 19 (PDF 20), §4 Profits and equation (5)

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace EssCheck.Accuracy

theorem revenues_foc {n : ℕ} (M : Model n) (hS : M.Standing)
    (β xh : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hx0 : 0 < xh) (hx1 : xh < 1) :
    (∀ i, (IsHybrid M β xh i →
      revH M β xh i = M.αbar * M.v i - zt M i * M.l i) ∧
      (¬ IsHybrid M β xh i → revH M β xh i = M.αbar * M.v i)) ∧
    (∀ i, (IsHybrid M β xh i → revL M β xh i = M.l i) ∧
      (¬ IsHybrid M β xh i → revL M β xh i = M.αbar * M.v i)) ∧
    piH M β xh - piL M β xh = privateWedge M (hybridSet M β xh) β := by sorry

end EssCheck.Accuracy
