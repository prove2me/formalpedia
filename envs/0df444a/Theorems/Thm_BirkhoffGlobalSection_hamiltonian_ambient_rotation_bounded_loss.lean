-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_ambient_rotation_bounded_loss
-- name    : BirkhoffGlobalSection.hamiltonian_ambient_rotation_bounded_loss
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:05:21.2554+00:00
-- url     : https://prove2.me/theorems/f974d303-a32c-4c8f-8431-22c5b406a3dd
-- title:
--   Positive momentum Hessian bounds ambient rotation loss
-- statement:
--   Let $F:\mathbb R^4\to\mathbb R$ be smooth near a complete Hamiltonian trajectory $x$. Assume its Hessian is strictly positive in every nonzero momentum direction along that trajectory:
--
--   $$
--   D^2F(x(t))[v,v]>0\qquad\text{whenever }v\ne0,\quad v_{q_1}=v_{q_2}=0.
--   $$
--
--   There is a universal constant $C>0$, independent of the Hamiltonian, trajectory, and time interval, such that every continuous ambient determinant angle $\alpha$ of the identity-normalized variational flow satisfies
--
--   $$
--   \alpha(b)-\alpha(a)\ge -C\qquad(a\le b).
--   $$
--
--   Here the ambient determinant is that of the complex-linear part in coordinates $q-ip$. No periodicity or saddle-center assumption is imposed. The bound controls the contribution from the complementary arc of a periodic orbit.
--
--   **Formalization Note** This is a determinant-angle consequence of the positive-vertical-crossing argument of Proposition 7.1, stated with positive definite momentum Hessian instead of its special identity-matrix case. The conversion from Lagrangian crossing estimates to this concrete determinant angle is included in the obligation.
-- source:
--   Liu–Salomão, https://arxiv.org/html/2506.17867v2#S7, Proposition 7.1 and its displayed positive vertical crossing-form computation, a consequence formulated for positive momentum Hessian. The concrete rotation map is from Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3). This is a derived determinant-angle bound, not a verbatim statement of the RS-index bound.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

/-- The positive momentum-Hessian crossing estimate, stated using the
continuous argument of the complex-linear determinant. The constant is
universal in real dimension four. No periodicity or saddle hypothesis is
needed. -/
theorem hamiltonian_ambient_rotation_bounded_loss :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Phase → ℝ) (x : ℝ → Phase),
        (∀ t : ℝ, ContDiffAt ℝ ∞ F (x t)) →
        (∀ t : ℝ, HasDerivAt x (hamiltonianVectorField F (x t)) t) →
        (∀ (t : ℝ) (v : Phase), v ≠ 0 → v 0 = 0 → v 1 = 0 →
          0 < fderiv ℝ (fun s => fderiv ℝ F s v) (x t) v) →
        ∀ Y : ℝ → (Phase →L[ℝ] Phase),
          IsHamiltonianVariationalSolution F x Y →
          ∀ α : ℝ → ℝ, IsAmbientRotationAngle Y α →
            ∀ a b : ℝ, a ≤ b → -C ≤ α b - α a := by sorry

end BirkhoffGlobalSection
