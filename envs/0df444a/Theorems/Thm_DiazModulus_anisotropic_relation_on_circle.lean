-- Prove2me | Theorems.Thm_DiazModulus_anisotropic_relation_on_circle
-- name    : DiazModulus.anisotropic_relation_on_circle
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T05:04:40.622993+00:00
-- url     : https://prove2.me/theorems/b305a4c1-11b6-40e9-b610-88db909c8e6f
-- title:
--   On every circle of algebraic radius greater than π, some point u off the axes with Im u ∉ ℚπ satisfies Re(u²) = π²
-- statement:
--   **An anisotropic relation occurs.**
--
--   Let $\rho > \pi^{2}$ be a real algebraic number. Then some $u$ with $|u|^{2} = \rho$, $\operatorname{Re} u \neq 0$ and $\operatorname{Im} u \notin \mathbb{Q}\pi$ satisfies
--
--   $$\tfrac12 u^{2} + \tfrac12 \bar u^{2} + (i\pi)^{2} = 0, \qquad\text{that is,}\qquad \operatorname{Re}(u^{2}) = \pi^{2}.$$
--
--   Take $u = x + iy$ with $x^{2} = (\rho + \pi^{2})/2$ and $y^{2} = (\rho - \pi^{2})/2$. If $y$ were a rational multiple of $\pi$, then $\pi^{2}$ would be algebraic.
--
--   The form $\tfrac12(X_1^{2} + X_2^{2}) + X_3^{2}$ is positive definite, so it has no non-trivial rational zero and `DiazModulus.anisotropic_relation_four_exp_barrier` applies. For these points $e^{u}$ is transcendental. Otherwise $u$, $\bar u$, $i\pi$ would be $\mathbb{Q}$-linearly independent logarithms of algebraic numbers in a field of transcendence degree one ($u$ is algebraic over $\mathbb{Q}(\pi)$) satisfying a non-trivial rational quadratic relation, which Théorème 0.2 of D. Roy and M. Waldschmidt (Ann. Sci. École Norm. Sup. 30, 1997) excludes. So the relation, invisible to $2\times2$ configurations, occurs only at points that are not candidates. (An earlier version of this text said that the transcendence of $e^{u}$ was not known; that was wrong.)
--
--   **Novelty.** None claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 5.7(c). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: D. Roy and M. Waldschmidt, Ann. Sci. École Norm. Sup. (4) 30 (1997) 753–796.

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem anisotropic_relation_on_circle (ρ : ℝ) (hρ : IsAlgebraic ℚ ρ)
    (hbig : Real.pi ^ 2 < ρ) :
    ∃ u : ℂ, u * conj u = (ρ : ℂ) ∧ u.re ≠ 0 ∧ (∀ q : ℚ, u.im ≠ (q : ℝ) * Real.pi) ∧
      (1 / 2 : ℂ) * u ^ 2 + (1 / 2 : ℂ) * conj u ^ 2 + (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 = 0 := by sorry

end DiazModulus
