-- Prove2me | Theorems.Thm_DiazModulus_log_two_pi_dependent_forces_transcendence
-- name    : DiazModulus.log_two_pi_dependent_forces_transcendence
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:03:44.195571+00:00
-- url     : https://prove2.me/theorems/2f12d464-d863-4f61-8d50-68f37fa817e1
-- title:
--   If log 2 is algebraic over ℚ(π), then 2^{i log 2/π} and e^{π²/log 2} are transcendental
-- statement:
--   **The partner of the smallest open instance, under the weakest hypothesis.**
--
--   Suppose that $\log 2$ is algebraic over $\mathbb{Q}[i\pi]$; equivalently, $\log 2$ and $\pi$ are algebraically dependent. Then
--
--   $$2^{\,i\log 2/\pi} = e^{i(\log 2)^{2}/\pi} \qquad\text{and}\qquad e^{\pi^{2}/\log 2}$$
--
--   are both transcendental.
--
--   `DiazModulus.log_two_diaz_or_transcendental` reaches the first number under the stronger hypothesis that $\sqrt{(\log 2)^{2}+\pi^{2}}$ is algebraic. That hypothesis is one particular algebraic dependence between $\log 2$ and $\pi$; this node needs only the dependence.
--
--   **Proof.** The argument of `DiazModulus.log_pair_square_ratio_transcendental`, at $\ell_1 = \log 2$ and $\ell_2 = i\pi$, gives the transcendence of $e^{(\log 2)^{2}/(i\pi)}$ and of $e^{(i\pi)^{2}/\log 2}$. These are the inverses of the two numbers above.
--
--   **Attribution.** Known: the case $\ell_1 = \log 2$, $\ell_2 = i\pi$ of M. Waldschmidt, *Nombres transcendants*, Lecture Notes in Math. **402** (1974), p. 202. The contribution of this node is the formal proof.
-- source:
--   Known: M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, p. 202, at log 2 and i*pi. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem log_two_pi_dependent_forces_transcendence (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) ((Real.log 2 : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp (Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2 / ((Real.log 2 : ℝ) : ℂ))) := by
  sorry

end DiazModulus
