-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned
-- name    : DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T10:38:35.392684+00:00
-- url     : https://prove2.me/theorems/acb73a81-a204-4a1f-95e1-4b56a878224f
-- title:
--   Irrational angle, period-aligned: a rational multiple of u has a two-point algebraic fibre
-- statement:
--   **One half of an ambient-space split of `DiazModulus.diaz_of_exp_not_real_irrational_angle`.**
--   The sibling half is `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free`; the two extra
--   hypotheses are literally complementary, so the reduction to the parent is a `by_cases` and carries
--   no mathematical content.
--
--   **The split predicate.** Write $\theta=\Im u$. The last hypothesis says
--   $$\exists\, r\in\mathbb Q^{\times}:\qquad \pi\,(\theta+r\pi)\in\overline{\mathbb Q}.$$
--
--   **What it means geometrically.** For $q\in\mathbb Q^{\times}$ and $n\in\mathbb Z$,
--   $$|qu+2\pi i n|^{2}-q^{2}|u|^{2}\;=\;4n\cdot\pi\bigl(q\theta+\pi n\bigr),$$
--   so, given that $|u|$ is algebraic, the predicate holds **exactly when some non-zero rational
--   multiple of $u$ has a second point of algebraic modulus in its exponential fibre**. That is
--   precisely the configuration of `Diaz.fibre_at_most_two` and of
--   `Diaz.nonreal_two_point_fibre_pi_sq`. The equivalence with the displayed arithmetic form is
--   machine-checked.
--
--   **Witness — the honesty check.** Both halves of the split are non-empty. A member of this one, in
--   closed form: put
--   $$\theta_A=\tfrac1\pi-\pi=-2.8232827674060025669\ldots,\qquad
--   u_A=\sqrt{16-\theta_A^{2}}+i\,\theta_A=2.8335621424751396494\ldots+i\,\theta_A .$$
--   Then $|u_A|=4$, $|u_A+2\pi i|=2\sqrt5$, $\pi(\theta_A+\pi)=1$, $\theta_A\notin\pi\mathbb Q$,
--   $\Re u_A\neq0$, $\Im u_A\neq 0$ and $e^{u_A}\notin\mathbb R$ — so $u_A$ satisfies every hypothesis
--   of this node. Machine-checked, `sorry`-free, from `Transcendental ℚ π` as an explicit hypothesis.
--
--   **Easier, or only weaker?** **Weaker**, as a quantifier shape. It is *not* known to be easier, and
--   no proof of it is claimed. What it is, is the half on which the mission's new rigidity machinery has
--   something to bite: the companion node `DiazModulus.recip_pi_log_of_period_aligned` proves,
--   unconditionally and with no transcendence input, that a counterexample lying in this half forces
--   some $\gamma\in\overline{\mathbb Q}^{\times}$ to have $\gamma/(i\pi)\in\mathcal L$. So this child
--   follows from
--   $$\gamma/(i\pi)\notin\mathcal L\quad\text{for every }\gamma\in\overline{\mathbb Q}^{\times},$$
--   a statement about $1/\pi$ alone, implied by the strong four exponentials conjecture and far more
--   special than the leaf. Whether it is provable is open.
--
--   **Hypotheses that are not load-bearing for that route.** The route lemma uses only
--   $\Im u\notin\pi\mathbb Q$, the split hypothesis, and the algebraicity of $e^{u}$. The clauses
--   `u ≠ 0`, `|u|` algebraic, `(exp u).im ≠ 0` and the off-axes clause are carried here **only** so
--   that the two children sum to the parent.
--
--   **Novelty.** Elementary once the parametrisation $u=\operatorname{Log}\alpha+2\pi i n$ is written
--   down; the geometric reading is in Corollary 3.4 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9) and the paragraph after it. Novelty is not asserted. Lean certifies correctness, not priority.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   Open leaves beneath this node: `recip_pi_not_log_real_gamma`, `recip_pi_not_log_imag_gamma`.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real_irrational_angle_period_aligned :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
