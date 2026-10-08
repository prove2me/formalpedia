-- Prove2me | Theorems.Thm_CouplingHMC_Exact_theorem_2_3
-- name    : CouplingHMC.Exact.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:51.41147+00:00
-- url     : https://prove2.me/theorems/d590e58e-ddda-49ba-9b79-53c94081b47c
-- title:
--   Theorem 2.3, p. 13 — for LT² ≤ min(K/L, 1/4, 1/(16Λ)), exact HMC satisfies E[f(R′(x,y))] ≤ (1−c) f(r(x,y)) with c of (32)
-- statement:
--   Suppose Assumption 2.1 is satisfied: $U\in C^4(\mathbb R^d)$ with $\int e^{-U}<\infty$, $U$ has a local minimum at $0$ with $U(0)=0$, $\|\nabla^2U\|\le L$, $\|\nabla^3U\|\le M$, $\|\nabla^4U\|\le N$, and $(x-y)\cdot(\nabla U(x)-\nabla U(y))\ge K|x-y|^2$ whenever $|x-y|\ge\mathcal R$, where $\mathcal R\ge0$ and $K>0$. Let $(q_t,p_t)$ be the exact Hamiltonian flow and fix $T\in(0,\infty)$ such that
--
--   $$LT^2\le\min\Bigl(\frac KL,\ \frac14,\ \frac1{16\Lambda}\Bigr),\qquad\Lambda=16L\mathcal R^2.$$
--
--   Let $\gamma=\min(T^{-1},\mathcal R^{-1}/4)$, $a=T^{-1}$, $R_1=\tfrac52(\mathcal R+T)$, $f(r)=\int_0^re^{-a\min(s,R_1)}ds$, and let $R'(x,y)=|q_T(x,\xi)-q_T(y,\eta)|$ be the distance after one step of the coupling (18)–(21), with $\xi\sim N(0,I_d)$ and $\tilde{\mathcal U}\sim\mathrm{Unif}(0,1)$ independent. Then for all $x,y\in\mathbb R^d$,
--
--   $$E\bigl[f(R'(x,y))\bigr]\le(1-c)\,f(|x-y|),\qquad c=\frac1{10}\min\Bigl(1,\frac12KT^2\Bigl(1+\frac{\mathcal R}{T}\Bigr)e^{-\mathcal R/(2T)}\Bigr)e^{-2\mathcal R/T}.$$
--
--   One step of exact HMC contracts the concave distance $\rho(x,y)=f(|x-y|)$ on average, for every pair of starting points, without global convexity of $U$. Iterating gives exponential convergence in the Kantorovich distance $\mathcal W_\rho$ (Corollary 2.8).
--
--   **Formalization Note.** The expectation is a Lebesgue integral of a nonnegative function with respect to the law of $(\xi,\tilde{\mathcal U})$. The constants are the paper's. For $\mathcal R=0$, $\gamma=T^{-1}$, and the coupling is then always synchronous.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Theorem 2.3, (31)–(32), p. 13, with (25)–(30) and §2.3

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- Theorem 2.3 (p. 13), with (31)–(32): under Assumption 2.1 and `LT² ≤ min(K/L, 1/4, 1/(16Λ))`,
with `γ`, `a`, `R₁` of (28)–(30), the coupling of §2.3 for exact HMC satisfies
`E[f(R'(x, y))] ≤ (1 - c) f(r(x, y))` for all `x, y`, with `c` of (32). -/
theorem theorem_2_3 {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (T : ℝ) (hT : 0 < T)
    (hTc : StepCond L K ℛ T) (x y : E d) :
    ∫⁻ ω, ENNReal.ofReal (fConc (aC T) (R1C T ℛ) (Rprime q T (gammaC T ℛ) ℛ x y ω))
        ∂(noiseLaw d) ≤
      ENNReal.ofReal ((1 - rateC K T ℛ) * fConc (aC T) (R1C T ℛ) ‖x - y‖) := by sorry

end CouplingHMC.Exact
