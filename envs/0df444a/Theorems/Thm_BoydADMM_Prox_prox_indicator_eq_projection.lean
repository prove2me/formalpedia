-- Prove2me | Theorems.Thm_BoydADMM_Prox_prox_indicator_eq_projection
-- name    : BoydADMM.Prox.prox_indicator_eq_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:32.19288+00:00
-- url     : https://prove2.me/theorems/64c27e17-0907-4cd5-b35d-fb1f3b397567
-- title:
--   §4.1, p. 26 — the proximity operator of the indicator of C is Π_C, for every ρ > 0
-- statement:
--   Let $\mathcal C\subseteq\mathbb R^n$ be a closed, nonempty, convex set and let $v\in\mathbb R^n$. Let $f$ be the indicator function of $\mathcal C$ ($f=0$ on $\mathcal C$, $f=+\infty$ off $\mathcal C$). Then:
--
--   1. the Euclidean projection $\Pi_{\mathcal C}(v)$ exists and is unique: there is exactly one $x\in\mathcal C$ with $\|v-x\|_2\le\|v-w\|_2$ for all $w\in\mathcal C$;
--   2. for every penalty $\rho>0$, a point $x$ is an $x$-update
--   $$x^+=\operatorname*{argmin}_x\Bigl(f(x)+\tfrac{\rho}{2}\|x-v\|_2^2\Bigr)$$
--   if and only if $x=\Pi_{\mathcal C}(v)$.
--
--   In particular $\mathbf{prox}_{f,\rho}(v)=\Pi_{\mathcal C}(v)$ independently of the choice of $\rho$. This is the reason that constraint sets in ADMM are handled by projections.
--
--   **Formalization Note** The indicator function is encoded as the domain $\mathcal C$ with the zero function. The book says "This holds independently of the choice of $\rho$"; we state it for every $\rho>0$, the book's standing assumption on $\rho$ (p. 14); at $\rho=0$ every point of $\mathcal C$ would be a minimizer.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 26, §4.1

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem prox_indicator_eq_projection {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_ne : C.Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∃! x, IsProjection C v x) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x, IsProx C (fun _ => 0) ρ v x ↔ IsProjection C v x := by sorry

end BoydADMM.Prox
