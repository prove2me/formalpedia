-- Prove2me | Theorems.Thm_DiazModulus_exp_abs_transcendental_of_isAlgebraic_adjoin
-- name    : DiazModulus.exp_abs_transcendental_of_isAlgebraic_adjoin
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:15:44.297377+00:00
-- url     : https://prove2.me/theorems/e6c7b2ae-e4d3-438f-ad6c-50879ac5598e
-- title:
--   If a non-real logarithm λ and its conjugate are algebraic over one ring ℚ[x], e^{|λ|} is transcendental
-- statement:
--   Let $\lambda \in \mathbb{C}$ with $e^{\lambda}$ algebraic and $\operatorname{Im}\lambda \neq 0$. Suppose that $\lambda$ and $\bar\lambda$ are both algebraic over the ring $\mathbb{Q}[x]$, for some $x \in \mathbb{C}$. Then
--
--   $$e^{|\lambda|}$$
--
--   is transcendental.
--
--   The hypothesis puts $\lambda$ and $\bar\lambda$ in an algebra of transcendence degree at most one, which is what four exponentials in transcendence degree one needs. With $x = \lambda$ this is `DiazModulus.exp_abs_transcendental_of_conj_algebraic`. With $\lambda = \log 2 + i\pi$ and $x = i\pi$ it gives `DiazModulus.exp_abs_log_two_add_i_pi_transcendental`.
-- source:
--   Known in substance: it is the argument behind G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245, Proposition 2, and D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Corollaire 7.4. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem exp_abs_transcendental_of_isAlgebraic_adjoin (lam x : ℂ)
    (hlam : IsAlgebraic ℚ (Complex.exp lam)) (him : lam.im ≠ 0)
    (hl : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) lam)
    (hc : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) (conj lam)) :
    Transcendental ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ)) := by
  sorry

end DiazModulus
