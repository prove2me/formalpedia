-- Prove2me | Theorems.Thm_EssCheck_Accuracy_welfare_formula
-- name    : EssCheck.Accuracy.welfare_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:06.184988+00:00
-- url     : https://prove2.me/theorems/7dea1355-e165-4161-8b55-9df077bfe798
-- title:
--   Equation (6) — primitive welfare simplifies at correct effort belief
-- statement:
--   Let $x\in(0,1)$ equal the implementer's expected effort and let $\beta\in[0,1)$. In every hybrid state with $p_i^0>0$, the unsuccessful firm's probability of offering the high royalty is
--   $$\tilde y_i=\frac{x p_i^H l_i}{(1-\beta)(1-x)p_i^0(\bar\alpha v_i-l_i)}.$$
--   Substituting this probability into welfare calculated from licensing payoffs, certification, and litigation gives equation (6):
--   $$w(\beta,x)=x\left[\sum_{i\in H}p_i^H\left(v_i-2\tilde z_i l_i\frac{\bar\alpha v_i}{\bar\alpha v_i-l_i}\right)+\sum_{i\in P}p_i^H v_i\right]+(1-x)\left[\sum_{i\in H}p_i^0v_i+\sum_{i\in P}p_i^0v_i\right]-c(x).$$
--   This identity exposes the paper's cancellation of the direct effect of accuracy on welfare while the regime partition is fixed.
--
--   **Formalization Note** The regime set is computed from $\beta$ and $x$ in every occurrence; it is not fixed by the definition of welfare.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), p. 21 (PDF 22), §4 Welfare and equation (6)

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace EssCheck.Accuracy

theorem welfare_formula {n : ℕ} (M : Model n) (hS : M.Standing)
    (β x : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (∀ i, IsHybrid M β x i → 0 < M.p0 i →
      yAt M β x i =
        x * M.pH i * M.l i /
          ((1 - β) * (1 - x) * M.p0 i * (M.αbar * M.v i - M.l i))) ∧
    welfare M β x =
      x * ((∑ i ∈ hybridSet M β x,
        M.pH i * (M.v i - 2 * zt M i * M.l i *
          (M.αbar * M.v i / (M.αbar * M.v i - M.l i)))) +
        (∑ i ∈ Finset.univ \ hybridSet M β x, M.pH i * M.v i)) +
      (1 - x) * ((∑ i ∈ hybridSet M β x, M.p0 i * M.v i) +
        (∑ i ∈ Finset.univ \ hybridSet M β x, M.p0 i * M.v i)) - M.c x := by sorry

end EssCheck.Accuracy
