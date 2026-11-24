-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_Supplement_packing_regret
-- name    : BayesProphet.MultiSec.Supplement.packing_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:09:03.85762+00:00
-- url     : https://prove2.me/theorems/b254a5dd-192c-4705-9646-e1aaf6f94f71
-- title:
--   Theorem 3 — constant regret of the Fluid Bayes Selector for Online Packing
-- statement:
--   Consider Online Packing with $d$ resources, $n$ types, consumption matrix $A\in\mathbb N^{d\times n}$ and rewards $r_j\ge0$, $r_{\max}=\max_j r_j$. Run the Fluid Bayes Selector (Algorithm 2) from initial budget $B\in\mathbb N^d$ over $T$ periods, with any selection of optimal solutions $X^t$ of the fluid LPs $(P_t)$. Let $\kappa>0$ be an LP Lipschitz constant of $A$ (Proposition 2).
--
--   1. **Multinomial arrivals.** If $\kappa$ is a Lipschitz constant w.r.t. $\|\cdot\|_1$ and arrivals are i.i.d. with type distribution $p$, $p_j>0$, $\sum_j p_j=1$, then for every $T$ and $B$
--   $$\mathbb E[\mathrm{Reg}]\ \le\ d\,r_{\max}\cdot 103\,\kappa^2\sum_{j\in[n]}\frac1{p_j}.$$
--   2. **General arrivals.** Let $\mu$ be a norm on $\mathbb R^n$, $\kappa$ a Lipschitz constant w.r.t. $\mu$, and let the arrival law satisfy the All-Time Deviation bound (7) w.r.t. $\mu$ and $\kappa_j=\kappa$ with constants $c_j\ge0$, $\tau_j\in\mathbb N$. Let $p_j\ge\mathbb P[\theta^t=j]$ for all $t\in[T]$, and let $\tilde\tau_j\in\mathbb N$ be such that $\mathbb E[Z_j(t)]\ge2$ for every $t\in[T]$ with $t\ge\tilde\tau_j$. Then for every $B$
--   $$\mathbb E[\mathrm{Reg}]\ \le\ d\,r_{\max}\sum_{j\in[n]}p_j\big(2c_j+\max\{\tau_j,\tilde\tau_j\}\big).$$
--
--   Neither bound depends on $T$ or $B$: the Fluid Bayes Selector has constant expected regret for multidimensional packing, for i.i.d. and for correlated or non-stationary arrivals satisfying the quadratic-tail condition (7). This extends Theorem 2 (one resource) to general consumption matrices.
--
--   **Formalization Note** Arrival laws are arbitrary distributions on $[n]^T$ (the multinomial law is the product law); expectations are finite sums. Regret is the full-information Bellman value minus Online's accrued reward, from the published generic online decision problem. The selection $X$ may break ties arbitrarily. Clause 1 does not repeat the hypothesis (7): over a finite horizon every law satisfies (7) for some constants (e.g. $c_j=T^2$), and the clause-1 bound involves none of them.
--
--   Differences from the source:
--   - reading: "for $\kappa=\kappa(A)$" given by Proposition 2 → Lean: every $\kappa>0$ with the Lipschitz property of Proposition 2 (w.r.t. $\|\cdot\|_1$ in clause 1, w.r.t. the norm $\mu$ of Eq. (7) in clause 2); reason: Proposition 2 only asserts existence of such a constant; the proof (pp. 20–21) uses the one-norm event $E_j$ and Eq. (8) for multinomial arrivals and only the Lipschitz property of $\kappa$.
--   - encoding: "$\tilde\tau_j$ is such that $\mathbb E[Z_j(\tilde\tau_j)]\ge2$" → Lean: $\mathbb E[Z_j(t)]\ge2$ for all $t\in[T]$ with $t\ge\tilde\tau_j$; reason: the process lives on $[T]$; for $\tilde\tau_j\le T$ the two are equivalent because $t\mapsto\mathbb E[Z_j(t)]$ is nondecreasing, and this is the property the proof uses ("vacuous for $t\ge\tilde\tau_j$").
--   - reading: rewards $r_j$ → Lean requires $r_j\ge0$; reason: rewards are the gains of serving requests in the model of Section 2.1 (Example 3 bounds compensations by $r_{\max}$); with all rewards negative the bound would be negative while regret is nonnegative.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), pp. 19–20, Theorem 3 (with Definition 5, Eq. (7), p. 19; Algorithm 2, p. 17; Proposition 2, p. 20)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals
import Definitions.Def_BayesProphet_MultiSec_Supplement_Packing

namespace BayesProphet.MultiSec.Supplement

theorem packing_regret {d n : ℕ} [NeZero n] (A : Fin d → Fin n → ℕ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) :
    (∀ κ : ℝ, 0 < κ → IsLPLipschitzConst A l1norm κ →
      ∀ p : Fin n → ℝ, (∀ j, 0 < p j) → ∑ j, p j = 1 →
      ∀ (T : ℕ) (B : Fin d → ℕ) (X : ℕ → (Fin d → ℕ) → Fin n → ℝ),
        IsPackingFluidSelection A r (multinomialWeight p T) X →
        packingExpectedRegret A r (multinomialWeight p T) X B ≤
          (d : ℝ) * packRmax r * (103 * κ ^ 2 * ∑ j, 1 / p j)) ∧
    (∀ μ : Seminorm ℝ (Fin n → ℝ), (∀ y, μ y = 0 → y = 0) →
      ∀ κ : ℝ, 0 < κ → IsLPLipschitzConst A μ κ →
      ∀ (T : ℕ) (w : (Fin T → Fin n) → ℝ), IsArrivalLaw w →
      ∀ (c : Fin n → ℝ) (τ τ' : Fin n → ℕ) (p : Fin n → ℝ),
        AllTimeDeviation w μ (fun _ => κ) c τ →
        (∀ j, ∀ t ∈ Finset.Icc 1 T, τ' j ≤ t → 2 ≤ meanCount w t j) →
        (∀ j, ∀ t ∈ Finset.Icc 1 T, probL w (fun θ => θ t = j) ≤ p j) →
      ∀ (B : Fin d → ℕ) (X : ℕ → (Fin d → ℕ) → Fin n → ℝ),
        IsPackingFluidSelection A r w X →
        packingExpectedRegret A r w X B ≤
          (d : ℝ) * packRmax r * ∑ j, p j * (2 * c j + (max (τ j) (τ' j) : ℕ))) := by sorry

end BayesProphet.MultiSec.Supplement
