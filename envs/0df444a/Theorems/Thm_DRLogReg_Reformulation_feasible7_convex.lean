-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_feasible7_convex
-- name    : DRLogReg.Reformulation.feasible7_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:33:51.622615+00:00
-- url     : https://prove2.me/theorems/a27d2417-8d13-4ea2-b5ea-25791448e815
-- title:
--   §3.1, p. 4 — the feasible set of program (7) is convex for every norm
-- statement:
--   Let $\|\cdot\|$ be any norm on the finite-dimensional feature space $V$, let $\kappa > 0$, and let $(\hat x_i,\hat y_i)_{i=1}^N$ be training samples with $N \ge 1$. Then the feasible set of program (7),
--   $$\Big\{(\beta,\lambda,s) \;:\; l_\beta(\hat x_i,\hat y_i)\le s_i,\ \ l_\beta(\hat x_i,-\hat y_i)-\lambda\kappa\le s_i\ \ (i\le N),\ \ \|\beta\|_*\le\lambda\Big\},$$
--   is a convex set. Since the objective $\lambda\varepsilon + \frac1N\sum_i s_i$ is linear, (7) is a convex program.
--
--   The paper states that (7) is a *tractable* convex program for most commonly used norms; this item formalizes convexity only, which holds for every norm.
--
--   **Formalization Note.** Tractability (efficient solvability) is not formalized.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, §3.1 (sentence after Theorem 1)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- §3.1, p. 4 (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic Regression*,
NIPS 2015): "Note that (7) constitutes a tractable convex program for most commonly
used norms ‖ · ‖." The feasible set of program (7) is convex (its objective is linear), for every
norm on the feature space. Tractability is not formalized. -/
theorem feasible7_convex
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) :
    Convex ℝ (feasible7 κ xhat yhat) := by sorry

end DRLogReg.Reformulation
