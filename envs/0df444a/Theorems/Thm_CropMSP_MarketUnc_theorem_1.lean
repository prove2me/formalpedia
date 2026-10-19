-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_theorem_1
-- name    : CropMSP.MarketUnc.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:03.672791+00:00
-- url     : https://prove2.me/theorems/a4792d95-edbb-4bc9-8637-30394f6bccc2
-- title:
--   Theorem 1, p. 10 — equilibrium crop production under market uncertainty
-- statement:
--   Let $\tau_0=(a-(1-2\alpha)\theta)/2$ and $\tau(m)=\min\{1,\max\{m,\tau_0\}\}$. Under the paper's standing assumptions, for an admissible MSP $m$, $\tau(m)$ is the unique equilibrium production quantity:
--
--   $$q(m)=\tau(m).$$
--
--   Apart from the boundary cost $c=\tau(m)$, a farmer with cost $c\in[0,1]$ sows exactly when $c\le\tau(m)$. Aggregate production is weakly increasing across admissible MSPs. This identifies the equilibrium on which the welfare equations depend.
--
--   **Formalization Note** Admissibility is evaluated at the proposed equilibrium quantity $\tau(m)$; the theorem establishes that this quantity is the equilibrium. The farmer-level biconditional excludes $c=\tau(m)$: when $\tau_0<m\le1$, the farmer at $c=m$ does not meet the weak VaR rule, although the paper's text includes that boundary point. A single cost has zero farmer mass, so the aggregate quantity is unaffected.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 10, Theorem 1; p. 37, proof

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem theorem_1 (P : Params) (hS : P.Standing) (m : ℝ)
    (hAdm : Admissible P m (tau P m)) :
    IsEquilibrium P m (tau P m) ∧
    (∀ q, IsEquilibrium P m q → q = tau P m) ∧
    (∀ c ∈ Set.Icc (0 : ℝ) 1, c ≠ tau P m →
      (Lucrative P m (tau P m) c ↔ c ≤ tau P m)) ∧
    (∀ m' : ℝ, Admissible P m' (tau P m') →
      m ≤ m' → tau P m ≤ tau P m') := by sorry

end CropMSP.MarketUnc
