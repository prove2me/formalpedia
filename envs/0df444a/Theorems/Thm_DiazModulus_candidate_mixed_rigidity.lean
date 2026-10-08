-- Prove2me | Theorems.Thm_DiazModulus_candidate_mixed_rigidity
-- name    : DiazModulus.candidate_mixed_rigidity
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-04T18:32:34.686954+00:00
-- url     : https://prove2.me/theorems/778ee6fb-417e-413f-9290-d3cc0e0ea607
-- title:
--   For a candidate u and a logarithm μ outside ℚu ∪ ℚū, the numbers u, μ and e^{uū/μ} generate transcendence degree at least two
-- statement:
--   Let $u$ be a candidate for Diaz's conjecture and $\mu$ a logarithm of an algebraic number with $\mu \notin \mathbb{Q}u \cup \mathbb{Q}\bar u$. Then $u, \mu, e^{u\bar u/\mu}$ generate a $\mathbb{Q}$-algebra of transcendence degree at least $2$.
--
--   This is Theorem 3.9 of C. Perassi's unpublished manuscript on Diaz's modulus conjecture. When $\mu$ is algebraic over $\mathbb{Q}(u)$ it gives the transcendence of $e^{|u|^2/\mu}$, which is `DiazModulus.candidate_norm_div_log_not_log`. On the two excluded rays the transcendence degree is one. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** Apply Waldschmidt's theorem (`DiazModulus.two_algebraically_independent_of_exp_column`) to $x = (u, \mu)$ and $y = (\bar u/\mu, 1)$. Both pairs are linearly independent over $\mathbb{Q}$ because $\mu \notin \mathbb{Q}u \cup \mathbb{Q}\bar u$, and the column $y_2 = 1$ gives the algebraic numbers $e^u$ and $e^\mu$. So two of $u, \mu, \bar u/\mu, 1, e^{u\bar u/\mu}, e^u, e^{\bar u}, e^\mu$ are algebraically independent. All eight are algebraic over $\mathbb{Q}(u, \mu, e^{u\bar u/\mu})$, since $\bar u = |u|^2/u$ with $|u|^2$ algebraic.
--
--   **Novelty.** Not asserted. It is Waldschmidt's Corollary 4 (1973, p. 192) at $(u, \bar u, \mu)$; see also Waldschmidt, LN 402, Exercise 7.4.d (p. 223), and Roy and Waldschmidt (1997, Cor. 1.2(c), p. 757).
-- source:
--   Theorem 3.9 of C. Perassi, unpublished manuscript on Diaz's modulus conjecture (August 2026). Known: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Cor. 4 (p. 192), at (u, ū, μ); M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, Ex. 7.4.d (p. 223); D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Cor. 1.2(c) (p. 757). Formal proof: Diaz modulus mission, 4 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_mixed_rigidity (u : ℂ) (hu : IsCandidate u) (μ : ℂ)
    (hμ : IsAlgebraic ℚ (Complex.exp μ))
    (hne : ∀ q : ℚ, μ ≠ (q : ℂ) * u ∧ μ ≠ (q : ℂ) * conj u) :
    2 ≤ Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({u, μ, Complex.exp (u * conj u / μ)} : Set ℂ)) := by
  sorry

end DiazModulus
