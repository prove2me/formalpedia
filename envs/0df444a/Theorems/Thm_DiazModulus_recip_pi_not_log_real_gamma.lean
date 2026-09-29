-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log_real_gamma
-- name    : DiazModulus.recip_pi_not_log_real_gamma
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T17:17:43.940499+00:00
-- url     : https://prove2.me/theorems/29c99457-7126-417f-bc91-69ee8b4ec42a
-- title:
--   No real algebraic multiple of $1/(i\pi)$ is a logarithm of an algebraic number
-- statement:
--   For every **real** algebraic $\gamma \neq 0$, the number $e^{\gamma/(i\pi)} = e^{-i\gamma/\pi}$ is transcendental.
--
--   Equivalently: $1/\pi$ is not an algebraic multiple of a *purely imaginary* logarithm of an algebraic number. Because $\gamma$ is real, $\lambda = \gamma/(i\pi)$ is purely imaginary, so $|e^{\lambda}| = 1$ and the hypothetical algebraic value lies on the unit circle. It cannot be a root of unity: $e^{-i\gamma/\pi} = e^{2\pi i k/n}$ would give $-\gamma/\pi = 2\pi(k/n + m)$, hence $\gamma \in \pi^{2}\mathbb{Q}$, forcing $\pi^{2}$ algebraic unless $\gamma = 0$. So this half asks for the transcendence of a number that would be an algebraic point of modulus one which is not a root of unity — the Gelfond--Schneider-shaped half of the split.
--
--   **How this sits under its parent.** The parent is `DiazModulus.recip_pi_not_log` (`b5a16bec-19d1-48b7-bd3b-09e62db3e432`): no non-zero algebraic $\gamma$ has $\gamma/(i\pi) \in \mathcal{L}$. This node and its sibling `DiazModulus.recip_pi_not_log_imag_gamma` **together imply the parent**, and each is strictly weaker in quantifier shape.
--
--   That the two halves suffice is *not* a case distinction — the real axis and the imaginary axis do not cover $\overline{\mathbb{Q}}^{\times}$. It is a consequence of the structure of
--   $$S_0 = \{\gamma \in \overline{\mathbb{Q}} : \gamma/(i\pi) \in \mathcal{L}\},$$
--   which is a $\mathbb{Q}$-subspace of $\overline{\mathbb{Q}}$ closed under complex conjugation: closed under addition because $e^{\lambda+\mu}=e^{\lambda}e^{\mu}$, under $\mathbb{Q}^{\times}$-scaling because $e^{(a/b)\lambda}$ is a root of $X^{b}-(e^{\lambda})^{a}$, and under conjugation because $\overline{i\pi}=-i\pi$, so that $\overline{\gamma}/(i\pi) = -\overline{\gamma/(i\pi)}$ and $e^{\overline{\gamma}/(i\pi)} = \overline{e^{\gamma/(i\pi)}}^{\,-1}$. Hence if $\gamma \in S_0$ then $\operatorname{Re}\gamma \in S_0$ and $i\operatorname{Im}\gamma \in S_0$, and $\gamma \neq 0$ forces one of them to be non-zero. The reduction is formalised and `sorry`-free.
--
--   **Strength.** Weaker than the parent, not known to be easier. Neither child is closable with anything in the environment, and neither is known to imply the other. Both follow from the strong four exponentials conjecture by the parent's own argument, applied to $x=(1,\lambda)$, $y=(1,i\pi)$.
--
--   **Honesty check.** The ambient class of this node is a set of algebraic numbers, so it is inhabited outright — no conjecture is involved in witnessing it. Witness: $\gamma = 1$, which is algebraic, non-zero and real. Neither half is provably constant and neither is conjecturally vacuous; this is the first leaf of the mission for which the honesty check is free rather than delicate.
--
--   **No redundant hypotheses.** All three of $\gamma$ algebraic, $\gamma \neq 0$ and the axis condition are used.
-- source:
--   Real-axis half of DiazModulus.recip_pi_not_log (b5a16bec-19d1-48b7-bd3b-09e62db3e432), obtained from the conjugation-stability of the Q-subspace {gamma in Qbar : gamma/(i pi) in L}. Implied by the strong four exponentials conjecture; see Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Ch. 11.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_not_log_real_gamma :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
