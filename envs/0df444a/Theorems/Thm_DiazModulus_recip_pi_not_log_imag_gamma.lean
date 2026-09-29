-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log_imag_gamma
-- name    : DiazModulus.recip_pi_not_log_imag_gamma
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T17:17:49.634071+00:00
-- url     : https://prove2.me/theorems/dea45a44-ff22-44f0-a052-a8bfad04c35c
-- title:
--   $e^{\beta/\pi}$ is transcendental for every non-zero real algebraic $\beta$
-- statement:
--   For every **purely imaginary** algebraic $\gamma \neq 0$ --- that is, $\gamma = i\beta$ with $\beta$ a non-zero real algebraic number --- the number $e^{\gamma/(i\pi)} = e^{\beta/\pi}$ is transcendental.
--
--   Equivalently: $1/\pi$ is not an algebraic multiple of a *real* logarithm of an algebraic number; equivalently again, $\pi \neq \beta/\log\alpha$ for any non-zero real algebraic $\beta$ and any real algebraic $\alpha > 0$, $\alpha \neq 1$. Because $\gamma$ is purely imaginary, $\lambda = \gamma/(i\pi)$ is real, so $e^{\lambda}$ is real and positive, and $\neq 1$ since $\lambda \neq 0$. This is the half containing the single number $e^{1/\pi}$, and it is the Hermite--Lindemann-shaped half of the split.
--
--   **How this sits under its parent.** The parent is `DiazModulus.recip_pi_not_log` (`b5a16bec-19d1-48b7-bd3b-09e62db3e432`): no non-zero algebraic $\gamma$ has $\gamma/(i\pi) \in \mathcal{L}$. This node and its sibling `DiazModulus.recip_pi_not_log_real_gamma` **together imply the parent**, and each is strictly weaker in quantifier shape.
--
--   That the two halves suffice is *not* a case distinction — the real axis and the imaginary axis do not cover $\overline{\mathbb{Q}}^{\times}$. It is a consequence of the structure of
--   $$S_0 = \{\gamma \in \overline{\mathbb{Q}} : \gamma/(i\pi) \in \mathcal{L}\},$$
--   which is a $\mathbb{Q}$-subspace of $\overline{\mathbb{Q}}$ closed under complex conjugation: closed under addition because $e^{\lambda+\mu}=e^{\lambda}e^{\mu}$, under $\mathbb{Q}^{\times}$-scaling because $e^{(a/b)\lambda}$ is a root of $X^{b}-(e^{\lambda})^{a}$, and under conjugation because $\overline{i\pi}=-i\pi$, so that $\overline{\gamma}/(i\pi) = -\overline{\gamma/(i\pi)}$ and $e^{\overline{\gamma}/(i\pi)} = \overline{e^{\gamma/(i\pi)}}^{\,-1}$. Hence if $\gamma \in S_0$ then $\operatorname{Re}\gamma \in S_0$ and $i\operatorname{Im}\gamma \in S_0$, and $\gamma \neq 0$ forces one of them to be non-zero. The reduction is formalised and `sorry`-free.
--
--   **Strength.** Weaker than the parent, not known to be easier. Neither child is closable with anything in the environment, and neither is known to imply the other. Both follow from the strong four exponentials conjecture by the parent's own argument, applied to $x=(1,\lambda)$, $y=(1,i\pi)$.
--
--   **Honesty check.** The ambient class of this node is a set of algebraic numbers, so it is inhabited outright — no conjecture is involved in witnessing it. Witness: $\gamma = i$, which is algebraic (a root of $X^{2}+1$), non-zero and purely imaginary. Neither half is provably constant and neither is conjecturally vacuous; this is the first leaf of the mission for which the honesty check is free rather than delicate.
--
--   **No redundant hypotheses.** All three of $\gamma$ algebraic, $\gamma \neq 0$ and the axis condition are used.
-- source:
--   Imaginary-axis half of DiazModulus.recip_pi_not_log (b5a16bec-19d1-48b7-bd3b-09e62db3e432), obtained from the conjugation-stability of the Q-subspace {gamma in Qbar : gamma/(i pi) in L}. Implied by the strong four exponentials conjecture; see Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Ch. 11.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_not_log_imag_gamma :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.re = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
