-- Prove2me | Theorems.Thm_AIMInventory_UnknownRho_theorem_8
-- name    : AIMInventory.UnknownRho.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:52.037322+00:00
-- url     : https://prove2.me/theorems/97c08b75-0242-428d-9bca-02501cc8351f
-- title:
--   Theorem 8 — for any γ, Λ₂(T) ≤ (max{b,h}ȳ/T){⌈(m/ρ′)²⌉ + E[K(ρ′, 2√2m²/ρ′)]} + 2hm E[|J₁(ρ′)|²]/√T
-- statement:
--   Consider a lost-sales inventory system with i.i.d. nonnegative demands $D_1,D_2,\dots$ of finite positive mean, holding cost $h>0$ and penalty $b>0$, and expected one-period cost $Q(y)=h\,E[y-D_1]^+ + b\,E[D_1-y]^+$. Excess inventory is non-perishable. The manager knows an upper bound $\bar y>0$ on the newsvendor quantity, $y^{NV}=\inf\{y\ge0: P(D_1\le y)\ge b/(b+h)\}\le\bar y$, and runs the AIM algorithm with an arbitrary step scale $\gamma>0$ and any initial target $\hat y_1\in[0,\bar y]$, producing targets $\hat y_t$ and implemented levels $y_t=\max\{\hat y_t,x_t\}$. Let
--   $$m=\frac{h\gamma\bar y}{\max\{b,h\}},\qquad \Lambda_2(T)=E\Big[\frac1T\sum_{t=1}^T\big(Q(y_t)-Q(\hat y_t)\big)\Big].$$
--   Let $K(\theta,z)=\min\{t\ge0: z+\sum_{s=1}^t(\theta-D_s)\le0\}$ be the hitting time of $(-\infty,0]$ by the random walk started at $z$ with increments $\theta-D_s$, and let $|J_1(\theta)|$ be the length of the first busy period of the queue $W_1(\theta)=0$, $W_{t+1}(\theta)=[W_t(\theta)+\theta-D_t]^+$.
--
--   Then for every $T\ge1$ and every $\rho'$ with $0<\rho'<\min\{m,E[D_1]\}$,
--   $$\Lambda_2(T)\le\frac{\max\{b,h\}\,\bar y}{T}\Big\{\big\lceil(m/\rho')^2\big\rceil+E\Big[K\Big(\rho',\frac{2\sqrt2\,m^2}{\rho'}\Big)\Big]\Big\}+\frac{2hm\,E\big[|J_1(\rho')|^2\big]}{\sqrt T}.$$
--
--   The cost of AIM splits as $\Lambda_1(T)+\Lambda_2(T)$, where $\Lambda_1(T)$ is controlled by stochastic subgradient descent for every $\gamma$. Theorem 8 controls the remaining term without the restriction $\gamma\le\rho\max\{b,h\}/(h\bar y)$ of Theorem 2, so the manager does not need a lower bound on mean demand: whenever $E[K(\cdot,\cdot)]$ and $E[|J_1(\cdot)|^2]$ are finite, the bound is $O(1/\sqrt T)$.
--
--   **Formalization Note.** The right side is computed in $[0,\infty]$: $E[K]$ and $E[|J_1|^2]$ are Lebesgue integrals that may be $\infty$, in which case the bound is trivially true rather than vacuous through a junk value; the left side $\Lambda_2(T)$ is a real Bochner integral of a bounded integrand, embedded with `ENNReal.ofReal` (a negative $\Lambda_2(T)$ embeds as $0$, consistent with the real inequality). The hypotheses $\rho'>0$, $h,b,\bar y,\gamma>0$ are implicit in the paper ("for any choice of the parameter $\gamma$" means any $\gamma>0$, as in (4)) and are added explicitly. The newsvendor bound $y^{NV}\le\bar y$ is the theorem's standing hypothesis and is kept although the bound does not use it.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 13, Theorem 8

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.UnknownRho

/-- Theorem 8, p. 13: the non-perishable AIM excess-cost bound for any
positive step scale `γ`. The right side is in `ℝ≥0∞`, so an infinite
hitting-time or busy-period expectation makes the bound infinite rather than
junk. `0 < ρ′` is added (the printed bound divides by `ρ′`). -/
theorem theorem_8 (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hNV : LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law c.h c.b ≤
      Real.toNNReal c.barY)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    (hmean : ρ' < CappedBaseStock.mean P) :
    ENNReal.ofReal (lambdaTwo P c T) ≤
      ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) *
        ((Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ')) +
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by sorry

end AIMInventory.UnknownRho
