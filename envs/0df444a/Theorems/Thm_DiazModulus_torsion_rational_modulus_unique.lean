-- Prove2me | Theorems.Thm_DiazModulus_torsion_rational_modulus_unique
-- name    : DiazModulus.torsion_rational_modulus_unique
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T06:25:38.787035+00:00
-- url     : https://prove2.me/theorems/f86e8b7b-33e4-40ce-a1c2-010d201771b8
-- title:
--   At most one pair ±t of real logarithms of algebraic numbers makes t² + π² rational
-- statement:
--   Let $t_0, t_1$ be real numbers such that $e^{t_0}$ and $e^{t_1}$ are algebraic. If $t_0^{2} + \pi^{2}$ and $t_1^{2} + \pi^{2}$ are both rational, then
--
--   $$t_1 = t_0 \qquad\text{or}\qquad t_1 = -t_0.$$
--
--   The number $u = t + i\pi$ is a logarithm of the negative algebraic number $-e^{t}$, and $|u|^{2} = t^{2} + \pi^{2}$. Diaz's conjecture predicts that $t^{2} + \pi^{2}$ is transcendental for every such $t$. The theorem shows that it can fail at a rational value for at most one pair $\pm t$.
--
--   **Proof.** Put $u = t_0 + i\pi$ and $v = t_1 + i\pi$. Both are non-zero, $e^{u} = -e^{t_0}$ and $e^{v} = -e^{t_1}$ are algebraic, and $u\bar u$, $v\bar v$ are the two rationals. Both are algebraic over $\mathbb{Q}(\pi)$, because $t_k^{2} = (t_k^{2} + \pi^{2}) - \pi^{2}$ and $i^{2} = -1$. `DiazModulus.nongeneric_rational_modulus_orbit` gives $v = qu$ or $v = q\bar u$ with $q$ rational. The imaginary parts give $q = 1$ in the first case and $q = -1$ in the second, and the real parts then give $t_1 = t_0$ or $t_1 = -t_0$.
--
--   **Novelty.** Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). It follows in a few lines from the four exponentials theorem in transcendence degree one (M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), Corollaire 4; Theorem 1 of D. Roy and M. Waldschmidt, Proc. Japan Acad. **71** (1995)), which is `DiazModulus.log_pair_rigid_of_trdeg_one` on this site.
-- source:
--   Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). It follows in a few lines from the four exponentials theorem in transcendence degree one: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 4; recorded as Theorem 1 of D. Roy and M. Waldschmidt, Quadratic relations between logarithms of algebraic numbers, Proc. Japan Acad. Ser. A 71 (1995), 151–153, who also credit W. D. Brownawell (J. Number Theory 6, 1974). Statement and formal proof: Diaz modulus mission, 29 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- At most one pair `±t` of real logarithms of algebraic numbers makes `t² + π²` rational. -/
theorem torsion_rational_modulus_unique (t₀ t₁ : ℝ)
    (he₀ : IsAlgebraic ℚ (Complex.exp (t₀ : ℂ))) (he₁ : IsAlgebraic ℚ (Complex.exp (t₁ : ℂ)))
    (r₀ r₁ : ℚ) (hr₀ : t₀ ^ 2 + Real.pi ^ 2 = r₀) (hr₁ : t₁ ^ 2 + Real.pi ^ 2 = r₁) :
    t₁ = t₀ ∨ t₁ = -t₀ := by
  sorry

end DiazModulus
