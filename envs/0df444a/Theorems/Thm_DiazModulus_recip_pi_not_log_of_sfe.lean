-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log_of_sfe
-- name    : DiazModulus.recip_pi_not_log_of_sfe
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T19:07:50.089613+00:00
-- url     : https://prove2.me/theorems/f812a768-18d6-4dab-b39a-7be82b3db489
-- title:
--   Strong four exponentials implies that no algebraic multiple of $1/(i\pi)$ is a logarithm
-- statement:
--   The strong four exponentials conjecture implies `DiazModulus.recip_pi_not_log`: that no non-zero algebraic $\gamma$ has $\gamma/(i\pi)$ a logarithm of an algebraic number.
--
--   **The configuration.** Write $\lambda = \gamma/(i\pi)$ and suppose $e^{\lambda}$ is algebraic. Apply the strong four exponentials conjecture to
--
--   $$x = (1,\ \lambda), \qquad y = (1,\ i\pi).$$
--
--   The four products are $1$, $i\pi$, $\lambda$, and $\lambda \cdot i\pi = \gamma$. All four lie in $\widetilde{\mathcal{L}}$: the first by definition; $i\pi$ because $e^{i\pi} = -1$ is algebraic; $\lambda$ by the assumption being contradicted; and $\gamma$ because it is algebraic, and $\widetilde{\mathcal{L}}$ is a $\overline{\mathbb{Q}}$-vector space containing $1$. That contradicts the conjecture, provided both rows are $\overline{\mathbb{Q}}$-linearly independent.
--
--   **What supplies the independence, and it is not $\pi$-transcendence.** Both $(1,\lambda)$ and $(1,i\pi)$ are independent as soon as $\lambda$ and $i\pi$ are transcendental, and **Hermite–Lindemann alone gives both** — no separate input on the transcendence of $\pi$ is needed. For $i\pi$: it is non-zero, and if it were algebraic then $e^{i\pi} = -1$ would be transcendental. For $\lambda$: it is non-zero since $\gamma \neq 0$, and if it were algebraic then $e^{\lambda}$ would be transcendental, against the assumption. Hermite–Lindemann is available on this mission as the Proved node `DiazModulus.hermite_lindemann_holds`, so it is discharged rather than carried, and the strong four exponentials conjecture is the only hypothesis this node retains.
--
--   **Attribution.** Up to scaling a row by $\gamma$, this is the matrix M. Waldschmidt uses at $\Lambda = i\pi$ for Consequence 1.6 of *Variations on the six exponentials theorem* (2005): under the strong four exponentials conjecture, $1/\Lambda \notin \widetilde{\mathcal{L}}$ for every transcendental $\Lambda \in \widetilde{\mathcal{L}}$. At $\Lambda = i\pi$ that consequence says $1/\pi \notin \widetilde{\mathcal{L}}$, which is stronger than (S).
--
--   **What it is for.** `DiazModulus.recip_pi_not_log` is open and two further open leaves of Diaz's modulus conjecture reduce to it. This node records exactly what strength would settle it, and pins that strength to a named conjecture rather than to a vague appeal. It does not make the parent easier: the strong four exponentials conjecture is open, and is itself the assumption the whole modulus conjecture currently rests on.
-- source:
--   The four-exponentials configuration x = (1, gamma/(i*pi)), y = (1, i*pi): up to scaling a row, the matrix of the proof of Consequence 1.6 in M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (R. Tandon, ed.), Hindustan Book Agency, 2005, at Lambda = i*pi. Independence of both rows follows from Hermite-Lindemann alone. The strong four exponentials conjecture: D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Conjecture 11.17.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_not_log_of_sfe :
    StrongFourExponentials →
      ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
        ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
