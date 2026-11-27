-- Prove2me | Theorems.Thm_EquivalencePrinciple_local_minkowski_first_order
-- name    : EquivalencePrinciple.local_minkowski_first_order
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T00:58:16.788027+00:00
-- url     : https://prove2.me/theorems/31ba68cd-d182-40c3-b41d-c15854a66c30
-- title:
--   The Equivalence Principle: local Minkowski form to first order
-- statement:
--   **The Einstein equivalence principle, local-flatness form — the goal theorem.**
--
--   Let `S` be a metric spacetime: a twice continuously differentiable field of symmetric nondegenerate bilinear forms of Lorentz signature $(-,+,+,+)$ on $\mathbb{R}^4$, with carried congruence and inverse witnesses, and let `p` be any point of spacetime.
--
--   **Conclusion:** there exists a twice continuously differentiable change of coordinates $\varphi : \mathbb{R}^4 \to \mathbb{R}^4$ such that
--
--   1. $\varphi(p) = 0$;
--   2. the first derivative of $\varphi$ at $p$ is invertible (a genuine, nondegenerate change of coordinates);
--   3. the pulled-back metric at $0$, $(\varphi^* g)_{ij}(0) = \sum_{a,b} \partial_i\varphi^a(0)\, \partial_j\varphi^b(0)\, g_{ab}(0)$ — the metric components in the new coordinates, evaluated at the image of `p` — is Minkowski up to a further constant invertible congruence: there is an invertible matrix $B$ with $B^T (\varphi^*g)(0) B = \mathrm{diag}(-1,1,1,1)$;
--   4. **all first derivatives of the pulled-back metric vanish at $0$**: the differential of $q \mapsto (\varphi^*g)_{ij}(q)$ at $0$ is the zero linear map, i.e. $\partial_k (\varphi^* g)_{ij}(0) = 0$ for all indices.
--
--   In words: at every point of a metric spacetime one can choose (twice continuously differentiable) coordinates in which, at that point, the metric is Minkowski **and** has no first-order corrections — Riemann normal coordinates to first order. Locally, to first order, gravity can be transformed away: a freely falling laboratory cannot detect the gravitational field by any first-order experiment on the metric. This is the mathematical core of Einstein's 1907 "complete physical equivalence of a gravitational field and a corresponding acceleration of the reference system".
--
--   **Formalization note.** The value half alone is the milestone `normal_value` (zeroth-order flatness, carried by the signature witness); the content of the goal is the vanishing of the first derivatives, which requires the quadratic correction term in the coordinate change built from the Christoffel symbols at the point. The local-Lorentz and local-position invariance legs of the Einstein principle (outcomes of laboratory experiments) and the strong form (self-gravitating bodies) are out of scope, as documented in the mission description.
-- source:
--   Wikipedia, Equivalence principle, https://en.wikipedia.org/wiki/Equivalence_principle (source of the quoted statements, reproduced verbatim in the definition file) (Einstein equivalence principle); A. Einstein, Uber das Relativitatsprinzip und die aus demselben gezogenen Folgerungen, Jahrbuch der Radioaktivitat und Elektronik 4 (1907), 411-462 ('complete physical equivalence of a gravitational field and a corresponding acceleration of the reference system'); C. W. Misner, K. S. Thorne, J. A. Wheeler, Gravitation (1973), Riemann normal Coordinates

import Mathlib
import Definitions.Def_EquivalencePrinciple

namespace EquivalencePrinciple

open Matrix

/-- The Einstein equivalence principle, local-flatness form — the goal.  At
every point of a metric spacetime there is a twice continuously differentiable
change of coordinates which makes the metric Minkowski at the point **and**
removes all of its first derivatives there — Riemann normal coordinates to
first order.  This is the mathematical core of Einstein's 1907 "complete
physical equivalence of a gravitational field and a corresponding acceleration
of the reference system": locally, to first order, gravity can be transformed
away — a freely falling laboratory cannot detect the gravitational field by any
first-order experiment on the metric.  The value half is `normal_value`; the
content is the vanishing of the first derivatives, which needs the quadratic
correction term built from the Christoffel symbols at the point. -/
theorem local_minkowski_first_order (S : Spacetime) (p : Sp) :
    ∃ φ : Sp → Sp, ContDiff ℝ 2 φ ∧ φ p = 0 ∧
      IsUnit ((Matrix.of fun a i => fderiv ℝ φ p (stdBasis i) a).det) ∧
      (∃ B : Matrix (Fin 4) (Fin 4) ℝ, IsUnit B.det ∧
        Bᵀ * (Matrix.of fun i j => pullbackMetric φ S.g 0 i j) * B
          = Matrix.diagonal minkowskiDiag) ∧
      fderiv ℝ (fun q i j => pullbackMetric φ S.g q i j) 0 = 0 := by
  sorry

end EquivalencePrinciple
