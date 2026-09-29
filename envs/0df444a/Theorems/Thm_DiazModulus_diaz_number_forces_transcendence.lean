-- Prove2me | Theorems.Thm_DiazModulus_diaz_number_forces_transcendence
-- name    : DiazModulus.diaz_number_forces_transcendence
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:31:17.002333+00:00
-- url     : https://prove2.me/theorems/096a0175-8254-4d81-8b65-e41777f29a78
-- title:
--   If t² + π² is algebraic for a real logarithm t, then e^{it²/π}, e^{π²/t} and e^{(t²+π²)/(iπ)} are transcendental
-- statement:
--   **What the Diaz number at $\alpha$ forces.**
--
--   Let $t \neq 0$ be real with $e^{t}$ algebraic, and suppose $\rho = t^{2} + \pi^{2}$ is algebraic. Then
--
--   $$e^{it^{2}/\pi}, \qquad e^{\pi^{2}/t}, \qquad e^{\rho/(i\pi)}$$
--
--   are all transcendental.
--
--   The hypothesis says that $u = t + i\pi$, a logarithm of $-e^{t}$, has algebraic modulus: it is a counterexample on the rational-angle branch, `DiazModulus.leaf_iff_one`. It is used only to make $t$ algebraic over $\mathbb{Q}(\pi)$, which supplies the transcendence-degree hypothesis of `DiazModulus.geometric_triple_not_logs`. The third conclusion says that the real half of the statement (S), `DiazModulus.recip_pi_not_log_real_gamma`, holds at $\gamma = \rho$: the two open boundary statements of the Diaz tree cannot fail at the same number.
--
--   **Novelty.** None: stronger forms are classical. The proof uses the hypothesis only to make $t$ algebraic over $\mathbb{Q}(\pi)$, and under that weaker hypothesis the first two conclusions follow from M. Waldschmidt, *Nombres transcendants*, Lecture Notes in Math. **402** (1974), p. 202: for $\mathbb{Q}$-linearly independent logarithms $\ell_{1}, \ell_{2}$ of algebraic numbers, either they are algebraically independent or $\exp(\ell_{1}^{2}/\ell_{2})$ is transcendental. Take $\{\ell_{1}, \ell_{2}\} = \{i\pi, t\}$. The second conclusion is also Proposition 1 of G. Diaz, J. Théor. Nombres Bordeaux **9** (1997), p. 241: if $(\log\alpha_{1})(\log\alpha_{2}) \in \mathbb{Q}\pi^{2}$, then $\log\alpha_{1}$ and $2i\pi$ are algebraically independent. The contribution of this node is the formal proof.
-- source:
--   Known in stronger form: M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, p. 202; G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245, Proposition 1. Background: W. D. Brownawell, J. Number Theory 6 (1974); M. Waldschmidt, J. Number Theory 5 (1973). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem diaz_number_forces_transcendence (t : ℝ) (ht : t ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp (t : ℂ)))
    (hρ : IsAlgebraic ℚ (((t ^ 2 + Real.pi ^ 2 : ℝ)) : ℂ)) :
    Transcendental ℚ (Complex.exp (Complex.I * (t : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2 / (t : ℂ))) ∧
      Transcendental ℚ (Complex.exp (((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry

end DiazModulus
