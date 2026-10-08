-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_p67_margin
-- name    : CachonCoord.DemandUpdate.p67_margin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:53.684601+00:00
-- url     : https://prove2.me/theorems/7d3e49fa-e6f8-4ea2-a512-8a38ffc84b01
-- title:
--   §6.6.1, p. 67 — w₂ − c₂ = w₁ − (λc₁ + (1 − λ)c₂) < w₁ − c₁ (strict for λ < 1)
-- statement:
--   With a coordinating contract ($\lambda \in [0,1]$, $p - b = \lambda p$, $w_2 - b = \lambda c_2$ and $w_1 - w_2 + \lambda c_2 = \lambda c_1$), the supplier's period-2 margin is
--   $$w_2 - c_2 = w_1 - \big(\lambda c_1 + (1-\lambda)c_2\big).$$
--   Since $c_1 < c_2$, it is strictly below the period-1 margin $w_1 - c_1$ when $\lambda < 1$, and equal to it when $\lambda = 1$.
--
--   Later production gives the retailer a valuable service, yet coordination forces a smaller margin on it.
--
--   **Formalization Note** The page prints "$< w_1 - c_1$" for all $\lambda \in [0,1]$. At $\lambda = 1$ the two margins are equal, so strictness is stated for $\lambda < 1$ and equality for $\lambda = 1$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, p. 67, the margin display

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

/-- Cachon (2003), 3rd draft, §6.6.1, p. 67 (the margin display). With a coordinating contract
(`λ ∈ [0, 1]`, `w_2 − b = λc_2`, `w_1 − w_2 + λc_2 = λc_1`) the supplier's period-2 margin is
`w_2 − c_2 = w_1 − (λc_1 + (1 − λ)c_2)`; it is strictly below the period-1 margin `w_1 − c_1` when
`λ < 1` and equal to it when `λ = 1`. -/
theorem p67_margin (M : Model) (lam w1 w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by sorry

end CachonCoord.DemandUpdate
