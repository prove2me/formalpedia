-- Prove2me | Theorems.Thm_DiazModulus_log_two_log_three_not_both_rational
-- name    : DiazModulus.log_two_log_three_not_both_rational
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T06:25:17.703735+00:00
-- url     : https://prove2.me/theorems/d986305f-8b22-40ab-a976-4f96f69de56e
-- title:
--   (log 2)² + π² and (log 3)² + π² are not both rational
-- statement:
--   The numbers
--
--   $$(\log 2)^{2} + \pi^{2} \qquad\text{and}\qquad (\log 3)^{2} + \pi^{2}$$
--
--   are not both rational.
--
--   They are the squared moduli of $\log 2 + i\pi$ and $\log 3 + i\pi$, logarithms of $-2$ and $-3$, and Diaz's conjecture predicts that both are transcendental. Their difference is $(\log 3)^{2} - (\log 2)^{2} = \log\tfrac{3}{2}\cdot\log 6$, so the statement can be read as: if $(\log 2)^{2} + \pi^{2}$ is rational, then $\log\tfrac{3}{2}\cdot\log 6$ is irrational.
--
--   **Proof.** $e^{\log 2} = 2$ and $e^{\log 3} = 3$ are algebraic, so `DiazModulus.torsion_rational_modulus_unique` would give $\log 3 = \pm\log 2$. Both logarithms are positive and $\log 2 < \log 3$.
--
--   **Novelty.** Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). The only mention of $(\log 2)^{2} + \pi^{2}$ found there is the example after Corollary 7.4 of Roy–Waldschmidt (1997): if $\log 2$ and $\pi$ are algebraically dependent, then $e^{\sqrt{(\log 2)^{2} + \pi^{2}}}$ is transcendental (compare `DiazModulus.exp_abs_log_two_add_i_pi_transcendental`). Other nodes about $\log 2$ and $\log 3$: `DiazModulus.log_two_diaz_or_transcendental` and `DiazModulus.pi_log_two_or_pi_log_three_transcendental`.
-- source:
--   Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). It follows from `DiazModulus.torsion_rational_modulus_unique`, that is, from the four exponentials theorem in transcendence degree one: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 4; recorded as Theorem 1 of D. Roy and M. Waldschmidt, Quadratic relations between logarithms of algebraic numbers, Proc. Japan Acad. Ser. A 71 (1995), 151–153, who also credit W. D. Brownawell (J. Number Theory 6, 1974). For (log 2)² + π² compare D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, the example after Corollary 7.4. Statement and formal proof: Diaz modulus mission, 29 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- The numbers `(log 2)² + π²` and `(log 3)² + π²` are not both rational. -/
theorem log_two_log_three_not_both_rational :
    ¬ ∃ r s : ℚ, Real.log 2 ^ 2 + Real.pi ^ 2 = r ∧ Real.log 3 ^ 2 + Real.pi ^ 2 = s := by
  sorry

end DiazModulus
