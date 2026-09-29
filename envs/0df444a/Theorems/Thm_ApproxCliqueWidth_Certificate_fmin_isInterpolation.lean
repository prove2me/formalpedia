-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_fmin_isInterpolation
-- name    : ApproxCliqueWidth.Certificate.fmin_isInterpolation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:32:04.305979+00:00
-- url     : https://prove2.me/theorems/6e157855-64ce-4ce1-a1e5-852fc2ed8ca7
-- title:
--   Proposition 4.2 — $f_{\min}$ is an interpolation of $f$
-- statement:
--   Let $V$ be a finite set and $f : 2^V \to \mathbb{Z}$ a submodular function such that $f(\emptyset) \le f(X)$ for all $X \subseteq V$. Then the function
--   $$f_{\min}(X, Y) = \min_{X \subseteq Z \subseteq V \setminus Y} f(Z), \qquad (X, Y) \in 3^V,$$
--   is an interpolation of $f$.
--
--   This guarantees that every submodular function with $\emptyset$ as a minimizer, in particular every symmetric submodular function with $f(\emptyset)=0$, has an interpolation, so the branch-width algorithm of Section 5 applies to it.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 519, Proposition 4.2

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Proposition 4.2 (p. 519). -/
theorem fmin_isInterpolation {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X) :
    IsInterpolation f (fmin f) := by sorry

end ApproxCliqueWidth.Certificate
