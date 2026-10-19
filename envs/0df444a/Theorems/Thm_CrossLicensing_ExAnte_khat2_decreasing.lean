-- Prove2me | Theorems.Thm_CrossLicensing_ExAnte_khat2_decreasing
-- name    : CrossLicensing.ExAnte.khat2_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:39.672855+00:00
-- url     : https://prove2.me/theorems/1d8b176d-ddb3-4ed5-94f4-f4cbf1b47a66
-- title:
--   Proof of Proposition 2, p. A.2 — the boundary threshold decreases to zero
-- statement:
--   Fix an inferior manufacturer's cost coefficient $k_1>49/144$. As licensing effectiveness increases through $[0,1]$, the cost threshold $\hat k_2(k_1\mid\beta)$ for a boundary duopoly strictly decreases, and at full effectiveness it reaches zero:
--
--   $$\beta<\beta'\quad\Longrightarrow\quad\hat k_2(k_1\mid\beta')<\hat k_2(k_1\mid\beta),\qquad \hat k_2(k_1\mid1)=0.$$
--
--   This orders the three cost regions in Proposition 4 and explains why the boundary region eventually disappears.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. A.2 (PDF 34), proof of Proposition 2, paragraph after the formula for k̂2

import Definitions.Def_CrossLicensing_ExAnte_Model

namespace CrossLicensing.ExAnte

/-- Proof of Proposition 2, p. A.2: the boundary threshold falls to zero. -/
theorem khat2_decreasing (k1 : ℝ) (hk1 : (49 : ℝ) / 144 < k1) :
    StrictAntiOn (fun β : ℝ => khat2 k1 β) (Set.Icc 0 1) ∧
      khat2 k1 1 = 0 := by sorry

end CrossLicensing.ExAnte
