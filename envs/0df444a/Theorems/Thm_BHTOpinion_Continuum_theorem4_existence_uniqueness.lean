-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_theorem4_existence_uniqueness
-- name    : BHTOpinion.Continuum.theorem4_existence_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:28.699399+00:00
-- url     : https://prove2.me/theorems/0caff93b-edb8-4fa6-ad85-64956236cf09
-- title:
--   Theorem 4 — for x̃_0 ∈ X_m^M the models (3.1) and (3.2) have a unique common solution, with slope ≥ m e^{−t} and regular at all times
-- statement:
--   Let $m,M>0$ and let the initial opinion function satisfy $\tilde x_0\in X_m^M$, i.e. $m\le\frac{\tilde x_0(\beta)-\tilde x_0(\alpha)}{\beta-\alpha}\le M$ for all $\beta\ne\alpha$ in $I=[0,1]$. Then there is a function $x$, $(\alpha,t)\mapsto x_t(\alpha)$, such that
--
--   1. $x$ is a solution of the integral equation (3.2) and of the differential equation (3.1) with initial condition $\tilde x_0$;
--   2. every solution of (3.2), and every solution of (3.1), with initial condition $\tilde x_0$ coincides with $x$ for all $t\ge0$ and all $\alpha\in I$;
--   3. for every $t\ge0$ and $\alpha<\beta$ in $I$,
--   $$m\,e^{-t}\le\frac{x_t(\beta)-x_t(\alpha)}{\beta-\alpha};$$
--   4. for every $t\ge0$, $x_t$ is regular: $x_t\in X_{m_t}^{M_t}$ for some $m_t,M_t>0$.
--
--   Regularity of the initial condition thus guarantees well-posedness of the continuum model, which may fail otherwise (a two-valued initial profile admits two different solutions), and it is preserved for all time.
--
--   **Formalization Note** The paper also prints the upper bound $\frac{x_t(\beta)-x_t(\alpha)}{\beta-\alpha}\le Me^{4t/m}$ for every $t$. Its proof (Appendix B) establishes this bound only on the first interval $[0,t_1]$, where $e^{t}\le 2$; the continuation restarts with the smaller rate $m_1=me^{-t_1}$, and the concatenated bound exceeds $Me^{4t/m}$. The statement therefore asserts what the proof supports and what the later results use, namely that $x_t$ is regular for all $t$ (the page: "admit a unique and common solution, which is regular at all times", p. 5225). The lower bound of (3.7) is stated as printed. Time is real with $t\ge0$; the derivative in (3.1) is one-sided at $t=0$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Theorem 4 and (3.7), p. 5225; proof in Appendix B, pp. 5236–5239

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem theorem4_existence_uniqueness (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (x0 : ℝ → ℝ) (hm0 : InXm m x0) (hM0 : InXM M x0) :
    ∃ x : ℝ → ℝ → ℝ, IsSolution x0 x ∧ IsDiffSolution x0 x ∧
      (∀ y : ℝ → ℝ → ℝ, IsSolution x0 y → ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, y t α = x t α) ∧
      (∀ y : ℝ → ℝ → ℝ, IsDiffSolution x0 y → ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, y t α = x t α) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, ∀ β ∈ I, α < β →
        m * Real.exp (-t) * (β - α) ≤ x t β - x t α) ∧
      (∀ t : ℝ, 0 ≤ t → Regular (x t)) := by sorry

end BHTOpinion.Continuum
