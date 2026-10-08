-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_lemmaA2
-- name    : BregmanPPA.IneqMult.lemmaA2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:18.909883+00:00
-- url     : https://prove2.me/theorems/3b320c8c-af7a-4de8-b5bb-4c505ebdcc99
-- title:
--   Lemma A2 — closed monotone conjugate and attained infimum
-- statement:
--   Let $F$ be a closed proper convex function, finite and subdifferentiable at a point of the strictly positive orthant. Its monotone conjugate $F^{*+}$ is closed, proper, and convex. At every point $z$ of its effective domain, the representation as an infimum over $w\ge z$ is attained:
--
--   $$\forall z\in\operatorname{dom}F^{*+},\quad\exists w\ge z:\quad F^{*+}(z)=F^*(w).$$
--
--   The result guarantees a genuine minimizing conjugate argument rather than only an infimum value.
--
--   **Formalization Note** Both conjugates are extended-real functions, and closedness is lower semicontinuity. The effective domain excludes $+\infty$; properness excludes $-\infty$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 223, Lemma A2, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.IneqMult

/-- Lemma A2, p. 223: closedness, convexity, properness and attainment of the
restricted conjugate's infimum representation. -/
theorem lemmaA2 {m : ℕ} (F : E m → EReal)
    (hproper : IsProperFn F) (hconvex : IsConvexFn F)
    (hclosed : LowerSemicontinuous F)
    (hu : ∃ u : E m, u ∈ posOrthant m ∧ F u ≠ ⊤ ∧
      ∃ v : E m, IsSubgradient F u v) :
    LowerSemicontinuous (monoConjE F) ∧
    IsProperFn (monoConjE F) ∧
    IsConvexFn (monoConjE F) ∧
    (∀ z : E m, monoConjE F z ≠ ⊤ →
      ∃ w : E m, (∀ i, z i ≤ w i) ∧ monoConjE F z = conjE F w) := by sorry

end BregmanPPA.IneqMult
