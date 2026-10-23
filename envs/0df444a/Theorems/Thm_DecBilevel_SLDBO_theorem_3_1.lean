-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_theorem_3_1
-- name    : DecBilevel.SLDBO.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:34.217896+00:00
-- url     : https://prove2.me/theorems/e56a340c-c679-4667-b8ff-60986f1e2a5e
-- title:
--   Theorem 3.1, p. 7 — SLDBO with small constant step sizes: O(1/K) stationarity and consensus errors
-- statement:
--   Fix constants $\sigma>0$, $L_{F,0},L_{F,1},L_{f,1},L_{f,2}\ge0$ and $\rho\in[0,1)$. There is a threshold $\bar\beta>0$; for every $\beta\in(0,\bar\beta)$ a threshold $\bar\eta>0$; and for every $\eta\in(0,\bar\eta)$ a threshold $\bar\alpha>0$, all depending only on these constants, with the following property. Let $0<\alpha<\bar\alpha$, and consider any instance of problem (6): $n\ge1$ agents with functions $F_i,f_i$ on $\mathbb R^p\times\mathbb R^q$ satisfying Assumption 2.1, a weight matrix $W$ satisfying Assumption 2.2 with this $\rho$, a map $y^*$ with $y^*(x)$ minimizing $f(x,\cdot)$ for every $x$ and $\Phi$ bounded below, and BOX 1 initial points $x^0,y^0,v^0$ with $\|v^0\|\le r_v$. Let Algorithm 1 run with step sizes $\alpha,\beta,\eta$. Then there is a constant $C$ such that for every integer $K\ge1$:
--
--   1. (Stationarity) $$\min_{0\le k\le K-1}\|\nabla\Phi(\bar x^k)\|^2\le\frac CK;$$
--   2. (Consensus error) $$\min_{0\le k\le K-1}\frac1n\sum_{i=1}^n\|x^k_i-\bar x^k\|^2\le\frac CK,\quad\min_{0\le k\le K-1}\frac1n\sum_{i=1}^n\|y^k_i-\bar y^k\|^2\le\frac CK,\quad\min_{0\le k\le K-1}\frac1n\sum_{i=1}^n\|v^k_i-\bar v^k\|^2\le\frac CK.$$
--
--   This is the paper's main result: the single-loop SLDBO reaches an $O(1/K)$ stationarity rate for decentralized bilevel optimization with no assumption on the heterogeneity of the agents' functions.
--
--   **Formalization Note.** (i) The paper requires the step sizes to satisfy the explicit bounds (62), p. 24. Those bounds do not make the Lyapunov coefficient $A_2$ of p. 23 nonnegative (a numerical check finds $A_2<0$, e.g. at $\sigma=0.2$, $\rho=1/2$, other constants $1$, $L_{f,2}=0$), so (62) as printed is not established by the paper's argument. The theorem is posed instead with nested step-size thresholds in the dependency order of (62) ($\bar\beta$; then $\bar\eta$ given $\beta$; then $\bar\alpha$ given $\beta,\eta$), chosen before the instance and uniform over all instances with the given constants. (ii) $\Phi$ bounded below (the paper's optimal value $F^*$, p. 4, being finite) is added; without it the claim fails, e.g. for $F_i(x,y)=-x$, $f_i(x,y)=y^2/2$, where $\nabla\Phi\equiv-1$. (iii) $\nabla\Phi$ is the formula (7) (`hypergrad`); "$=O(1/K)$" is read as one constant $C$, chosen after the instance and before $K$, with $\exists k<K$ standing for the minimum. (iv) The conventions of the Setting module apply (operator-norm Hessian blocks, $\rho$ any bound on $\mathbf 1^\perp$, Euclidean product norm).
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 7, Theorem 3.1; Algorithm 1 input p. 6; step sizes (62) p. 24 (replaced by thresholds)

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem theorem_3_1 (σ LF0 LF1 Lf1 Lf2 ρ : ℝ) (hσ : 0 < σ) (hLF0 : 0 ≤ LF0)
    (hLF1 : 0 ≤ LF1) (hLf1 : 0 ≤ Lf1) (hLf2 : 0 ≤ Lf2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ βbar > 0, ∀ β : ℝ, 0 < β → β < βbar →
    ∃ ηbar > 0, ∀ η : ℝ, 0 < η → η < ηbar →
    ∃ αbar > 0, ∀ α : ℝ, 0 < α → α < αbar →
    ∀ (n p q : ℕ), 0 < n → ∀ (W : Matrix (Fin n) (Fin n) ℝ) (F f : Fin n → E p → E q → ℝ)
      (ystar : E p → E q) (x0 : E p) (y0 v0 : E q),
      Assumption21 F f σ LF0 LF1 Lf1 Lf2 → Assumption22 W ρ →
      (∀ x, IsMinOn (avgf f x) Set.univ (ystar x)) →
      BddBelow (Set.range (Phi F ystar)) →
      ‖v0‖ ≤ rv σ LF0 →
      ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
        let s := run W F f α β η (rv σ LF0) x0 y0 v0
        (∃ k < K, ‖hypergrad F f ystar (avg (s k).x)‖ ^ 2 ≤ C / K) ∧
        (∃ k < K, (1 / (n : ℝ)) * ∑ i, ‖(s k).x i - avg (s k).x‖ ^ 2 ≤ C / K) ∧
        (∃ k < K, (1 / (n : ℝ)) * ∑ i, ‖(s k).y i - avg (s k).y‖ ^ 2 ≤ C / K) ∧
        (∃ k < K, (1 / (n : ℝ)) * ∑ i, ‖(s k).v i - avg (s k).v‖ ^ 2 ≤ C / K) := by sorry

end DecBilevel.SLDBO
