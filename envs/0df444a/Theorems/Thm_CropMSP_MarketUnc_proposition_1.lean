-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_proposition_1
-- name    : CropMSP.MarketUnc.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:04.21625+00:00
-- url     : https://prove2.me/theorems/0a09ebe4-96b9-4a7f-a89e-3f6a0e193d16
-- title:
--   Proposition 1, p. 13 — net benefit and net social value under market uncertainty
-- statement:
--   Under the paper's standing assumptions, consider only minimum support prices admissible at their equilibrium production quantities. Let $\tau_0=(a-(1-2\alpha)\theta)/2$.
--
--   1. If $a\le3/2$ and $\tau_0\le m\le1$, net benefit satisfies $B(m)\ge0$ exactly when $m\le2a/3$. The admissible MSP $m_B=\max\{\tau_0,\min\{1,a/3\}\}$ attains the maximum net benefit over all admissible MSPs. Net benefit is constant among admissible MSPs in the region $m\le\tau_0$, and likewise constant in the region $m\ge1$.
--   2. Net social value is strictly positive for every admissible MSP. The admissible MSP $m_V=\min\{1,a/2\}$ attains its maximum over all admissible MSPs.
--
--   In particular, the theorem identifies the policy levels optimizing the farmer-side net benefit and the broader social value under the paper's market uncertainty model.
--
--   **Formalization Note** Each maximizing clause includes existence of an equilibrium and admissibility at the claimed optimizer. “Attains the maximum” does not assert uniqueness. The additional explicit assumption $\theta>0$ makes the uniform shock and its normalization valid. Under the standing assumptions, $m\le2a/3$ already holds for every admissible $m\in[\tau_0,1]$ when $a\le3/2$; the paper's biconditional is retained as stated.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 13, Proposition 1; pp. 39–40, proof

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem proposition_1 (P : Params) (hS : P.Standing) :
    (P.a ≤ 3 / 2 → ∀ m q, IsEquilibrium P m q → Admissible P m q →
      tau0 P ≤ m → m ≤ 1 → (0 ≤ netBenefit P m q ↔ m ≤ 2 * P.a / 3)) ∧
    (∃ qB, IsEquilibrium P (max (tau0 P) (min 1 (P.a / 3))) qB ∧
      Admissible P (max (tau0 P) (min 1 (P.a / 3))) qB ∧
      ∀ m q, IsEquilibrium P m q → Admissible P m q →
        netBenefit P m q ≤
          netBenefit P (max (tau0 P) (min 1 (P.a / 3))) qB) ∧
    (∀ m q m' q', IsEquilibrium P m q → Admissible P m q →
      IsEquilibrium P m' q' → Admissible P m' q' →
      ((m ≤ tau0 P ∧ m' ≤ tau0 P) ∨ (1 ≤ m ∧ 1 ≤ m')) →
      netBenefit P m q = netBenefit P m' q') ∧
    (∀ m q, IsEquilibrium P m q → Admissible P m q →
      0 < netSocialValue P m q) ∧
    (∃ qV, IsEquilibrium P (min 1 (P.a / 2)) qV ∧
      Admissible P (min 1 (P.a / 2)) qV ∧
      ∀ m q, IsEquilibrium P m q → Admissible P m q →
        netSocialValue P m q ≤
          netSocialValue P (min 1 (P.a / 2)) qV) := by sorry

end CropMSP.MarketUnc
