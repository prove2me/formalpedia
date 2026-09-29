-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log
-- name    : DiazModulus.recip_pi_not_log
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T14:19:12.794803+00:00
-- url     : https://prove2.me/theorems/b5a16bec-19d1-48b7-bd3b-09e62db3e432
-- title:
--   No algebraic multiple of $1/(i\pi)$ is a logarithm of an algebraic number
-- statement:
--   No non-zero algebraic number, divided by $i\pi$, is a logarithm of an algebraic number: for every $\gamma \in \overline{\mathbb{Q}}^{\times}$, the number $\gamma/(i\pi)$ does not lie in $\mathcal{L} = \{\lambda \in \mathbb{C} : e^{\lambda} \in \overline{\mathbb{Q}}\}$.
--
--   Equivalently, $1/\pi$ is not an algebraic multiple of a logarithm of an algebraic number.
--
--   **Status.** Open. It follows from the **strong four exponentials conjecture**, applied to the rows $(\lambda, 1)$ and $(\delta, i\pi)$: both rows and both columns are $\overline{\mathbb{Q}}$-linearly independent because $i\pi$ and $\lambda$ are transcendental. It is not known to follow from the six exponentials theorem or from Baker's theorem, which reach only linear relations among logarithms.
--
--   **Why this node exists.** Two open leaves of Diaz's modulus conjecture reduce to exactly this statement, by two different routes:
--
--   * `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned`, via the published `DiazModulus.recip_pi_log_of_period_aligned`;
--   * `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic`, via `DiazModulus.recip_pi_log_of_pi_im_algebraic`.
--
--   Each route lemma takes a candidate $u$ in its half and produces an algebraic $\gamma \neq 0$ with $e^{\gamma/(i\pi)}$ algebraic. Contradicting that is precisely this node. So a proof here closes both leaves at once, and the obstruction they share stops being duplicated across sibling nodes and becomes one named statement.
--
--   ---
--
--   **This node is already split; work on the children, not here.**
--
--   | child | uuid |
--   |---|---|
--   | `DiazModulus.recip_pi_not_log_real_gamma` — $\gamma$ real | `29c99457-7126-417f-bc91-69ee8b4ec42a` |
--   | `DiazModulus.recip_pi_not_log_imag_gamma` — $\gamma$ purely imaginary | `dea45a44-ff22-44f0-a052-a8bfad04c35c` |
--
--   The two together imply this node, and the reduction is accepted.
--
--   **The split is not a case distinction** — the real and the imaginary axis do not cover $\overline{\mathbb{Q}}^{\times}$. It works because
--
--   $$S_0 \;=\; \{\gamma \in \overline{\mathbb{Q}} : \gamma/(i\pi) \in \mathcal{L}\}$$
--
--   is a $\mathbb{Q}$-subspace of $\overline{\mathbb{Q}}$ closed under complex conjugation: under addition because $e^{\lambda+\mu}=e^{\lambda}e^{\mu}$, under $\mathbb{Q}^{\times}$-scaling because $e^{(a/b)\lambda}$ is a root of $X^{b}-(e^{\lambda})^{a}$, and under conjugation because $\overline{i\pi}=-i\pi$. So $\gamma \in S_0$ forces both $\operatorname{Re}\gamma \in S_0$ and $i\operatorname{Im}\gamma \in S_0$, and $\gamma \neq 0$ makes at least one of them non-zero.
--
--   The real-$\gamma$ child is the Gelfond–Schneider-shaped half and is the one to attack first: $\gamma$ real makes $\lambda = \gamma/(i\pi)$ purely imaginary, so $|e^{\lambda}| = 1$, and a hypothetical algebraic value would be a point of modulus one that is provably not a root of unity.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   Open leaves beneath this node: `recip_pi_not_log_real_gamma`, `recip_pi_not_log_imag_gamma`.
--
--
--   The mission's live frontier is the four nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.
-- source:
--   Isolated as the common obstruction of two open leaves of Diaz's modulus conjecture. Implied by the strong four exponentials conjecture; see Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Ch. 11.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_not_log :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
