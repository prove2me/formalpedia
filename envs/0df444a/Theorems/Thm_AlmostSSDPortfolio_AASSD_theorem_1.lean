-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_theorem_1
-- name    : AlmostSSDPortfolio.AASSD.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:52.162372+00:00
-- url     : https://prove2.me/theorems/c69bb247-28ae-494d-aeb7-e742b94f1222
-- title:
--   Theorem 1, p. 12 — if a portfolio dominates the benchmark by τ-AASSD under some discretization scheme, it dominates it by τ-ASSD
-- statement:
--   Consider the finite-scenario portfolio model of §2 under its standing assumptions: returns in $[a,b]$ with $a<b$, scenario probabilities forming probability vectors. Let $\lambda\in\Lambda$ be a portfolio with return $X$, let $Y$ be the benchmark, and let $\tau\in(1,\infty)$.
--
--   If there exists a discretization scheme $D$ (grid $a=d_1<\dots<d_{T_D}=b$ containing every benchmark return) under which $X$ dominates $Y$ by $\tau$-AASSD, that is
--   $$2(\tau-1)\sum_{s=1}^{T_D-1}A_{D,s,\lambda}\le\mathrm{Var}(Y)+(b-\mathbb EY)^2-\mathrm{Var}(X)-(b-\mathbb EX)^2\quad\text{and}\quad\mathbb EX\ge\mathbb EY,$$
--   then $X$ dominates $Y$ by $\tau$-ASSD:
--   $$\tau\int_{S_2}\big(F^{(2)}_\lambda(t)-G^{(2)}(t)\big)\,dt\le\int_{\bar S_2}\big(G^{(2)}(t)-F^{(2)}_\lambda(t)\big)\,dt\quad\text{and}\quad\mathbb EX\ge\mathbb EY.$$
--   In short, $(\tau\text{-AASSD})\Rightarrow(\tau\text{-ASSD})$.
--
--   AASSD needs only means, variances and the LPM at finitely many grid points, so it can be imposed as a tractable constraint in portfolio optimization; this theorem guarantees that every portfolio it admits is a genuine $\tau$-ASSD improvement on the benchmark.
--
--   **Formalization Note.** Both dominance notions are written with their ratios cross-multiplied (Definition 3 in the paper's form (5d)); see the definition file for why this is the faithful reading when a denominator vanishes. $\bar S_2$ is the complement of $S_2$ inside $[a,b]$.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 12, Theorem 1

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem theorem_1 {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) (τ : ℝ) (hτ : 1 < τ)
    (h : ∃ D : Discretization S, D.IsAASSD lam τ) : S.IsASSD lam τ := by sorry

end AlmostSSDPortfolio.AASSD
