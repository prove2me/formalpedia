-- Prove2me | Theorems.Thm_DiazModulus_exp_abs_transcendental_of_conj_algebraic
-- name    : DiazModulus.exp_abs_transcendental_of_conj_algebraic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:02:56.11119+00:00
-- url     : https://prove2.me/theorems/26b4149e-66af-4604-972c-580232cc05a8
-- title:
--   If a non-real logarithm λ and its conjugate are algebraically dependent, e^{|λ|} is transcendental
-- statement:
--   **The modulus of a logarithm, in transcendence degree one.**
--
--   Let $\lambda$ be a non-real logarithm of an algebraic number, and suppose that $\bar\lambda$ is algebraic over $\mathbb{Q}[\lambda]$. Since $\lambda$ is transcendental, this is the same as saying that $\lambda$ and $\bar\lambda$ are algebraically dependent. Then
--
--   $$e^{|\lambda|}$$
--
--   is transcendental.
--
--   This is the homogeneous companion of Diaz's modulus conjecture. The conjecture asks that $|\lambda|$ never be algebraic; this node says that $|\lambda|$ is not a logarithm of an algebraic number, whenever $\lambda$ and $\bar\lambda$ generate a field of transcendence degree one. At $\lambda = i\pi$ it gives the transcendence of $e^{\pi}$. The case $\lambda = \log 2 + i\pi$ is `DiazModulus.exp_abs_log_two_add_i_pi_transcendental`.
--
--   **Proof.** The matrix $\begin{pmatrix} |\lambda| & \bar\lambda \\ \lambda & |\lambda| \end{pmatrix}$ has determinant $|\lambda|^{2} - \lambda\bar\lambda = 0$. If $e^{|\lambda|}$ were algebraic, its entries would be non-zero logarithms of algebraic numbers, all algebraic over $\mathbb{Q}[\lambda]$, so by `DiazModulus.four_exponentials_trdeg_one` its rows or its columns would be $\mathbb{Q}$-linearly dependent. Either way $\lambda$ would be a rational multiple of the real number $|\lambda|$, against $\operatorname{Im}\lambda \neq 0$.
--
--   **Attribution.** Known: Proposition 2 of G. Diaz, J. Théor. Nombres Bordeaux **9** (1997), and Corollaire 7.4 of D. Roy and M. Waldschmidt, Ann. Sci. École Norm. Sup. (4) **30** (1997), found independently the same year; see also Exercise 15.16(c) of Waldschmidt's *Diophantine Approximation on Linear Algebraic Groups* (2000). The node `Diaz.log_modulus_forces_independence` states it with the four exponentials theorem as an explicit hypothesis; this node is unconditional. The contribution of this node is the formal proof.
-- source:
--   Known: G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245, Proposition 2; D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Corollaire 7.4; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Exercise 15.16(c). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem exp_abs_transcendental_of_conj_algebraic (lam : ℂ)
    (hlam : IsAlgebraic ℚ (Complex.exp lam)) (him : lam.im ≠ 0)
    (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({lam} : Set ℂ))) (conj lam)) :
    Transcendental ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ)) := by
  sorry

end DiazModulus
