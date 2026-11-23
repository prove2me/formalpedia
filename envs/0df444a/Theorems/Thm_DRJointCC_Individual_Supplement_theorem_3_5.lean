-- Prove2me | Theorems.Thm_DRJointCC_Individual_Supplement_theorem_3_5
-- name    : DRJointCC.Individual.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:34:22.724945+00:00
-- url     : https://prove2.me/theorems/8452ff73-319a-4eea-9be7-5fc250ac2e74
-- title:
--   Theorem 3.5, p. 19 — the quadratic-majorant approximation equals the worst-case CVaR approximation: $\mathcal Z_Q^{\mathrm{JCC}}(\alpha)=\mathcal Z^{\mathrm{JCC}}(\alpha)$
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Consider the joint chance constraint with $m\ge1$ rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$. For scaling parameters $\alpha\in\mathcal A=\{\alpha\in\mathbb R^m:\alpha>0\}$ let
--
--   $$
--   \mathcal Z^{\mathrm{JCC}}(\alpha)=\Big\{x\in\mathbb R^n:\ \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\Big(\max_{i=1,\dots,m}\alpha_i\big(y_i^0(x)+y_i(x)^\top\tilde\xi\big)\Big)\le0\Big\}
--   $$
--
--   be the worst-case CVaR approximation (29), and $\mathcal Z_Q^{\mathrm{JCC}}(\alpha)$ the quadratic-majorant approximation (38). Then for every $\alpha\in\mathcal A$,
--
--   $$
--   \mathcal Z_Q^{\mathrm{JCC}}(\alpha)=\mathcal Z^{\mathrm{JCC}}(\alpha).
--   $$
--
--   Approximating the joint chance constraint by a worst-case CVaR constraint and approximating its max-function by a quadratic majorant therefore give the same feasible set.
--
--   Differences from the source:
--   - encoding: max_{i=1,…,m} with m ≥ 1 implicit → ⨆ over Fin m with the hypothesis 0 < m; reason: the max is the finite supremum for m ≥ 1; standing convention of the published 02 items
--   - encoding: worst-case CVaR, a real number or +∞ → extended-real CVaR with E_P[(L − β)^+] a lower Lebesgue integral (published cvar / wcCVaR); reason: Lean convention; +∞ is represented instead of a junk value; same instances
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 19, Theorem 3.5; p. 15, (29) (Z^JCC(α)); p. 18, (38)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Majorant

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- Theorem 3.5, p. 19: for every `α ∈ 𝒜` (componentwise positive), the quadratic-majorant
approximation equals the worst-case CVaR approximation: `𝒵_Q^JCC(α) = 𝒵^JCC(α)`. -/
theorem theorem_3_5 {m n k : ℕ} (hm : 0 < m) (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    ZQ D μ Sig ε α = DRJointCC.Joint.ZJCCα D μ Sig ε α := by sorry

end DRJointCC.Individual.Supplement
