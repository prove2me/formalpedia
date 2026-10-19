-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_boundary_solution
-- name    : CrossLicensing.Innovation.boundary_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:37.030491+00:00
-- url     : https://prove2.me/theorems/30efdb19-b6e5-42f2-affa-39dfbe218430
-- title:
--   Proof of Proposition 2, p. A.1 — the boundary candidate: T^B_2 = T̂2(T^B_1|β) and T^B_1 = T1(T^B_2)
-- statement:
--   Assume $0 \le \beta \le 1$, $49/144 < k_2 < k_1$, $\beta < \sqrt3 - 1$ and $k_2 < \hat k_2(k_1\mid\beta)$. Let
--   $$D_B = (4\sqrt3-7)(\beta-1)(\beta+1)(5\beta-7) - 48(\sqrt3\beta + \sqrt3 - 3)k_1,$$
--   $$T^B_2 = \frac{48(2\sqrt3-3)k_1 - (4\sqrt3-7)(\beta-1)(5\beta-7)}{D_B},\qquad T^B_1 = -\frac{(4\sqrt3-7)(\beta-1)(5\beta-7)}{D_B}.$$
--   Then
--
--   1. $D_B > 0$;
--   2. $T^B_2 = \hat T_2(T^B_1\mid\beta)$: manufacturer 2 sits exactly on the duopoly boundary;
--   3. manufacturer 1's duopoly first-order condition holds at $(T^B_1, T^B_2)$:
--   $$\frac{\partial}{\partial T_1}\Big[\tfrac1{144}\big((5\beta-7)T_1 + (5-7\beta)T^B_2 - 2\big)^2 - k_1T_1^2\Big]\Big|_{T_1 = T^B_1} = 0,$$
--   4. both boundary investments are nonnegative, and $T^B_1$ is manufacturer 1's best response to $T^B_2$ over every nonnegative innovation level, using the full innovation payoff after the supplier reprices.
--
--   These are the paper's boundary duopoly outcomes.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), proof of Proposition 2, p. A.1 (PDF 33)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem boundary_solution (β k1 k2 : ℝ) (h : Standing β k1 k2) (hβ : β < Real.sqrt 3 - 1)
    (hk : k2 < khat2 β k1) :
    0 < TBden β k1 ∧ TB2 β k1 = That2 β (TB1 β k1) ∧
    HasDerivAt (fun x => duoGross1 β x (TB2 β k1) - k1 * x ^ 2) 0 (TB1 β k1) ∧
    ∃ t1 t2 : NNReal, (t1 : ℝ) = TB1 β k1 ∧ (t2 : ℝ) = TB2 β k1 ∧
      ∀ x : NNReal, innovationPayoff1 β k1 x t2 ≤ innovationPayoff1 β k1 t1 t2 := by sorry

end CrossLicensing.Innovation
