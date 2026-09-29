-- Prove2me | Theorems.Thm_ConvexOptimization_barrier_method_sqrt_m_complexity_sc
-- name    : ConvexOptimization.barrier_method_sqrt_m_complexity_sc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-17T02:17:33.646273+00:00
-- url     : https://prove2.me/theorems/7ee3797b-6015-48cc-a842-1cff1d85fb4f
-- title:
--   Barrier method: $O(\sqrt{m}\log(1/\varepsilon))$ Newton steps
-- statement:
--   **Complexity of the barrier method with the $\sqrt{m}$ outer schedule** — Boyd & Vandenberghe §11.5, with the inner line search confined to the strictly feasible set.
--
--   Consider the inequality-constrained convex program
--   $$\text{minimize } f_0(x) \quad\text{subject to } f_i(x) \le 0,\ i = 1,\dots,m,$$
--   with $f_0$ and all $f_i$ convex and differentiable, and let $\varphi(x) = -\sum_i \log(-f_i(x))$ be the logarithmic barrier. Assume the §11.5.1 self-concordance hypothesis: $t f_0 + \varphi$ is self-concordant on the strictly feasible set for every $t \ge 0$, with positive definite Hessian and closed sublevel sets, and let $x^{\star}(t)$ denote the exact minimiser — the central path.
--
--   Run the barrier method with the outer schedule $\mu = 1 + 1/\sqrt m$ and $t_i = \mu^{i} t^{(0)}$, each centering step warm-started at the previous centre $x^{\star}(t_i)$ and carried out by damped Newton with backtracking. Then:
--
--   * each centering step reaches accuracy $\varepsilon_{\mathrm{nt}}$ within
--   $$\frac{20-8\alpha}{\alpha\beta(1-2\alpha)^2}\cdot\frac12 \;+\; \log_2\log_2(1/\varepsilon_{\mathrm{nt}}) \;+\; 2$$
--   Newton steps — a bound *independent of the outer index $i$, of $m$ and of $n$*. The reason is that the objective gap inherited from the previous centre is at most $m(\mu - 1 - \log\mu)$ by (11.25)–(11.26), and for $\mu = 1+1/\sqrt m$ the elementary estimate $\log(1+u)\ge u - u^2/2$ makes this at most $\tfrac12$;
--
--   * $\lceil \sqrt m \,\log_2(m/(t^{(0)}\varepsilon))\rceil$ outer iterations drive the duality gap $m/t$ below $\varepsilon$, because $\sqrt m\,\log_2\!\bigl(1+1/\sqrt m\bigr) \ge 1$ for $m \ge 1$.
--
--   Multiplying the two gives the $O(\sqrt m \log(1/\varepsilon))$ total Newton complexity that is the whole point of the barrier method.
--
--   **Formalization note.** Each centering run is governed by `IsDampedNewtonRunOn`, whose line search `IsBacktrackingStepOn` accepts the largest step $\beta^j$ whose trial point is **both** strictly feasible and Armijo-acceptable — exactly what B&V's convention "$f = +\infty$ off $\operatorname{dom} f$" (§9.1, p. 457) delivers. This must be said explicitly because `logBarrier` is real-valued and returns finite junk values off the strictly feasible set (Mathlib's `Real.log` is $0$ at $0$ and $\log|\cdot|$ on the negatives), so the barrier does *not* blow up there; the original formalization `ConvexOptimization.barrier_method_sqrt_m_complexity`, which used the unconfined line search, is false for this reason and has been disproved. Differentiability of $f_0$ and of each $f_i$ is assumed, as it is throughout B&V §11, since the central-path/duality argument behind (11.25)–(11.26) needs the individual gradients $\nabla f_i$ and not merely the gradient of the sum. A hypothesis that the sublevel sets of $t f_0 + \varphi$ within the strictly feasible set are closed is stated explicitly, as the Dikin-ellipsoid argument behind (9.55) needs it.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 585-590, §11.5 (complexity analysis via self-concordance), eqs. (11.25)-(11.26) and (11.30)-(11.32), with the line search read under the convention of §9.1, p. 457.

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_ConvexOptimization_IsDampedNewtonRunOn
import Definitions.Def_ConvexOptimization_logBarrier

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.barrier_method_sqrt_m_complexity_sc {n mI : ℕ} (hmI : 0 < mI)
    (α β t0 ε εnt : ℝ)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (ht0 : 0 < t0) (hε : 0 < ε) (hεnt0 : 0 < εnt) (hεnt : εnt < 1 / 4)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hf₀_diff : Differentiable ℝ f₀) (hfc_diff : ∀ i, Differentiable ℝ (fc i))
    (hSC : ∀ t : ℝ, 0 ≤ t →
      IsSelfConcordantOn {x | ∀ i, fc i x < 0}
        (fun x => t * f₀ x + logBarrier fc x))
    (hclosed : ∀ t : ℝ, 0 < t → ∀ c : ℝ,
      IsClosed {x | (∀ i, fc i x < 0) ∧ t * f₀ x + logBarrier fc x ≤ c})
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      HasGradientAt (fun y => t * f₀ y + logBarrier fc y) (g t x) x)
    (H : ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      HasFDerivAt (g t) (H t x) x)
    (hHpd : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      ∀ v, v ≠ 0 → 0 < ⟪H t x v, v⟫)
    (xc : ℝ → EuclideanSpace ℝ (Fin n))
    (hxc_str : ∀ t : ℝ, 0 < t → ∀ i, fc i (xc t) < 0)
    (hxc_min : ∀ t : ℝ, 0 < t →
      IsMinOn (fun x => t * f₀ x + logBarrier fc x) {x | ∀ i, fc i x < 0} (xc t)) :
    ∃ (w : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (K : ℕ → ℕ),
      (∀ i, w i 0 = xc ((1 + 1 / Real.sqrt mI) ^ i * t0)) ∧
      (∀ i, IsDampedNewtonRunOn {x | ∀ i', fc i' x < 0}
        (fun x => (1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 * f₀ x + logBarrier fc x)
        (g ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0))
        (H ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0)) α β (w i)) ∧
      (∀ i, ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 * f₀ (w i (K i)) +
          logBarrier fc (w i (K i))) -
        ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 *
            f₀ (xc ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0)) +
          logBarrier fc (xc ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0))) ≤ εnt) ∧
      (∀ i, (K i : ℝ) ≤
        (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) / 2 +
          Real.logb 2 (Real.logb 2 (1 / εnt)) + 2) ∧
      (mI : ℝ) / ((1 + 1 / Real.sqrt mI) ^
          ⌈Real.sqrt mI * Real.logb 2 (mI / (t0 * ε))⌉₊ * t0) ≤ ε := by
  sorry
