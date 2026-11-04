-- Prove2me | Theorems.Thm_AIMInventory_UnknownRho_restart_bound
-- name    : AIMInventory.UnknownRho.restart_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:30.370536+00:00
-- url     : https://prove2.me/theorems/5cf018c4-4774-4691-a5f2-7f163798536c
-- title:
--   Proof of Theorem 8 — E[K̃] ≤ ⌈(m/ρ′)²⌉ + E[K(ρ′, 2√2 m²/ρ′)]
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite positive mean, run the non-perishable AIM algorithm with scale $\gamma>0$, upper bound $\bar y>0$ and costs $h,b>0$, and put $m=h\gamma\bar y/\max\{b,h\}$. Let $Z_t(m)$ be the queue $Z_1(m)=0$, $Z_{t+1}(m)=[Z_t(m)+m/\sqrt t-D_t]^+$. For $0<\rho'<m$ let
--   $$\tilde T=\min\Big\{t\in\mathbb Z_+:\frac m{\sqrt t}\le\rho'\Big\},\qquad \tilde K=\min\{t>\tilde T: Z_t(m)=0\}\in\{1,2,\dots\}\cup\{\infty\},$$
--   and let $K(\theta,z)=\min\{t\ge0: z+\sum_{s=1}^t(\theta-D_s)\le0\}$ be the first time the random walk started at $z$ with increments $\theta-D_s$ enters $(-\infty,0]$. Then
--   $$E[\tilde K]\le\big\lceil(m/\rho')^2\big\rceil+E\Big[K\Big(\rho',\frac{2\sqrt2\,m^2}{\rho'}\Big)\Big].$$
--
--   Up to the deterministic time $\tilde T$, the queue $Z(m)$ is fed at least as fast as the walk with drift $\rho'-D$; after $\tilde T$ it is fed more slowly. The inequality bounds the expected time until the queue first empties after $\tilde T$, which is the length of the initial stretch of periods in which the cost gap $Q(y_t)-Q(\hat y_t)$ is bounded only by the trivial bound $\max\{b,h\}\bar y$.
--
--   **Formalization Note.** Both expectations are Lebesgue integrals in $[0,\infty]$, so the inequality is meaningful (and trivially true) when the right side is infinite; $\tilde K$ and $K$ take the value $\infty$ on paths where the defining set is empty. The hypothesis $\rho'>0$ is implicit in the paper (the bound divides by $\rho'$). Under $0<\rho'<m$, $\tilde T=\lceil(m/\rho')^2\rceil$.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 14, proof of Theorem 8 (display for E[K̃])

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.UnknownRho

/-- The displayed `E[K̃]` inequality in the proof of Theorem 8, p. 14.
Expectations retain `∞` on paths with no return. -/
theorem restart_bound (P : DemandLaw) (c : Parameters) (ρ' : ℝ)
    (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    (∫⁻ d, restartTime c ρ' d ∂CappedBaseStock.demandPathLaw P) ≤
      (Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ') := by sorry

end AIMInventory.UnknownRho
