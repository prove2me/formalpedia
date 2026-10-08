-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_lemmaA1
-- name    : BregmanPPA.IneqMult.lemmaA1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:12.378325+00:00
-- url     : https://prove2.me/theorems/1ef6313b-2100-4c5e-9811-df50fe70fb42
-- title:
--   Lemma A1 — no nonnegative recession direction of the conjugate
-- statement:
--   Let $F$ be a closed proper convex extended-valued function that is finite and subdifferentiable at some point of the strictly positive orthant. Then its ordinary conjugate $F^*$ has no nonzero recession direction in the nonnegative orthant:
--
--   $$y\ge0,\quad y\ne0\quad\Longrightarrow\quad y\text{ is not a recession direction of }F^*.$$
--
--   This exclusion supplies the attainment condition used in Lemma A2.
--
--   **Formalization Note** A recession direction is defined exactly by the paper's limit inferior criterion at every point of the effective domain. Closedness is lower semicontinuity of $F$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 223, Lemma A1, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.IneqMult

/-- Lemma A1, p. 223: no nonzero nonnegative recession direction of the conjugate. -/
theorem lemmaA1 {m : ℕ} (F : E m → EReal)
    (hproper : IsProperFn F) (hconvex : IsConvexFn F)
    (hclosed : LowerSemicontinuous F)
    (hu : ∃ u : E m, u ∈ posOrthant m ∧ F u ≠ ⊤ ∧
      ∃ v : E m, IsSubgradient F u v) :
    ∀ y : E m, y ∈ nonnegOrthant m → y ≠ 0 →
      ¬ IsRecessionDirection (conjE F) y := by sorry

end BregmanPPA.IneqMult
