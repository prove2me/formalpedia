-- Prove2me | Theorems.Thm_DiazModulus_log_two_diaz_or_transcendental
-- name    : DiazModulus.log_two_diaz_or_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:31:36.032325+00:00
-- url     : https://prove2.me/theorems/7adec0a4-f992-474c-a6ea-76c85788e9c9
-- title:
--   At least one of √((log 2)² + π²) and 2^{i log 2/π} is transcendental
-- statement:
--   **The smallest open instance of Diaz's conjecture.**
--
--   At least one of the two numbers
--
--   $$\sqrt{(\log 2)^{2} + \pi^{2}} \qquad\text{and}\qquad 2^{\,i\log 2/\pi} = e^{i(\log 2)^{2}/\pi}$$
--
--   is transcendental.
--
--   The first number is $|\log 2 + i\pi|$, the modulus of a logarithm of $-2$. Whether it is algebraic is the smallest open instance of Diaz's conjecture. This is the case $t = \log 2$ of `DiazModulus.diaz_number_forces_transcendence`. Neither number is known to be transcendental on its own.
--
--   **Novelty.** None: a stronger statement is classical. By M. Waldschmidt, *Nombres transcendants*, Lecture Notes in Math. **402** (1974), p. 202, applied to $\log 2$ and $i\pi$: either $\log 2$ and $\pi$ are algebraically independent, or $2^{\,i\log 2/\pi}$ is transcendental. The algebraicity of $\sqrt{(\log 2)^{2}+\pi^{2}}$ is one particular algebraic dependence. The contribution of this node is the formal proof.
-- source:
--   Known in stronger form: M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, p. 202 (at log 2 and i*pi). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem log_two_diaz_or_transcendental :
    Transcendental ℚ (Real.sqrt (Real.log 2 ^ 2 + Real.pi ^ 2)) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) := by sorry

end DiazModulus
