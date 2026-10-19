-- Prove2me | Theorems.Thm_CrossLicensing_ExAnte_boundary_preference
-- name    : CrossLicensing.ExAnte.boundary_preference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:39.788697+00:00
-- url     : https://prove2.me/theorems/74ae86f3-2026-4fc5-90fe-dfbdebca8496
-- title:
--   Proof of Proposition 4(i), p. A.2 — licensing weakly raises boundary-duopoly supplier profit
-- statement:
--   Fix $k_1>49/144$ and $0\le\beta\le1$. If the boundary-duopoly region is feasible, meaning $\hat k_2(k_1\mid\beta)>49/144$, then the printed supplier-profit expressions satisfy
--
--   $$\pi_s^B(0)\le\pi_s^B(\beta).$$
--
--   This is the algebraic comparison underlying Proposition 4(i); the equilibrium-profit result identifies each side with the optimized supplier revenue in its corresponding regime.
--
--   **Formalization Note** The paper phrases feasibility using a cost $k_2$ strictly between $49/144$ and $\hat k_2$. The Lean statement uses the equivalent nonemptiness condition on that interval, since $\pi_s^B$ itself is independent of $k_2$.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. A.2 (PDF 34), proof of Proposition 4(i)

import Definitions.Def_CrossLicensing_ExAnte_Model

namespace CrossLicensing.ExAnte

/-- Proof of Proposition 4(i), p. A.2, on the two boundary-duopoly formulas. -/
theorem boundary_preference (k1 β : ℝ)
    (hk1 : (49 : ℝ) / 144 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hregion : (49 : ℝ) / 144 < khat2 k1 β) :
    piBoundary 0 k1 ≤ piBoundary β k1 := by sorry

end CrossLicensing.ExAnte
