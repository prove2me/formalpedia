-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free
-- name    : DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T14:23:23.311285+00:00
-- url     : https://prove2.me/theorems/1b43101e-b00e-4168-9769-ddd07242b0c6
-- title:
--   Period-aligned, norm not a rational multiple of the aligned datum: the residual half
-- statement:
--   **One half of a split of `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned`.**
--   The sibling is `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free`;
--   the two extra hypotheses are literally complementary, so the reduction to the parent is a
--   `by_cases` and carries no mathematical content.
--
--   **Setting.** Write $\theta=\Im u$, $t=\Re u$, $A=\lVert u\rVert^{2}$. The parent's aligned
--   hypothesis gives a rational $r\neq0$ with $\beta:=\pi(\theta+r\pi)\in\overline{\mathbb Q}$;
--   $r$ is unique and $\beta\neq0$, because $\theta\notin\pi\mathbb Q$ and $\pi^{2}$ is
--   transcendental. So $\theta=\beta/\pi-r\pi$ and $\nu:=i(\theta+r\pi)=i\beta/\pi\neq0$.
--
--   **The split predicate** is $A\in\mathbb Q\cdot\beta$.
--
--   **This is where the difficulty of the aligned leaf now sits.** On the sibling half
--   $A\in\mathbb Q\cdot\beta$ the two certified products $u\bar u=A$ and
--   $\nu\cdot 2\pi i=-2\beta$ can be assembled into a $2\times2$ matrix over $\mathcal L$ with
--   vanishing determinant and $\mathbb Q$-independent rows and columns, so that half follows from
--   the four exponentials conjecture — and, since the configuration has transcendence degree one
--   over $\mathbb Q$, from the *known* transcendence-degree-one case of it
--   (`Diaz.four_exp_trdeg_one`). Here that is unavailable: the determinant
--   $$\det\begin{pmatrix}c_1u&c_2\nu\\ c_3\,2\pi i&c_4\bar u\end{pmatrix}
--   = c_1c_4A+2c_2c_3\beta$$
--   cannot be made to vanish with rational $c_i$, and the same holds for an arbitrary
--   $\lambda_i=x_iu+y_i\bar u+z_i\,2\pi i$ with $x_i,y_i,z_i\in\mathbb Q$: the vanishing of
--   $\lambda_1\lambda_4-\lambda_2\lambda_3$ forces either $A/\beta\in\mathbb Q$ or a matrix
--   whose rows or columns are $\mathbb Q$-proportional.
--
--   **Correction, 2026-09-08.** An earlier version of this description derived that last claim
--   "monomial by monomial in $1,t^{2},t/\pi,t\pi,\pi^{2}$", which presumes those five are
--   $\mathbb Q$-linearly independent. **They are not**, on this class: the aligned quartic
--   relation $t^{2}\pi^{2}+r^{2}\pi^{4}-(A+2r\beta)\pi^{2}+\beta^{2}=0$ is exactly a dependence
--   among them, and it is the same relation that puts the configuration in transcendence degree
--   one. The conclusion is nonetheless correct. The valid argument substitutes the quartic
--   relation and separates real and imaginary parts, and needs only
--   $\operatorname{Transcendental}_{\mathbb Q}\pi$, $\operatorname{Re}u\neq0$ and
--   $\beta\neq0$; it is machine-checked and published as
--   `DiazModulus.aligned_norm_free_no_rational_log_matrix`, which also shows the obstruction
--   extends to every $2\times2$ minor, so no rank-$\le1$ matrix over
--   $\operatorname{span}_{\mathbb Q}\{u,\bar u,2\pi i\}$ escapes it. Allowing algebraic coefficients widens the condition to
--   $A/\beta\in\overline{\mathbb Q}$, but that is the *strong* four exponentials conjecture.
--
--   So the split point $\mathbb Q$ versus $\overline{\mathbb Q}$ is exactly the boundary between
--   what the four exponentials statement can reach from the certified data and what it cannot.
--
--   **Witness — the honesty check.** With $\theta_A=1/\pi-\pi$ (so $r=1$, $\beta=1$) and
--   $u_C=\sqrt{16\sqrt2-\theta_A^{2}}+i\theta_A$ one has $\lVert u_C\rVert^{2}=16\sqrt2$, which is
--   algebraic and is **not** a rational multiple of $\beta=1$. All six clauses of this node hold
--   for $u_C$; machine-checked, `sorry`-free, from `Transcendental ℚ π` as an explicit hypothesis.
--   The sibling half is witnessed by the same angle with norm-square $16$.
--
--   **Strength.** Weaker than the parent as a quantifier shape; not known to be easier, and no
--   proof is claimed. What it is, is the residue of the aligned leaf after everything the four
--   exponentials statement can decide has been removed.
--
--   **Novelty.** Nothing here is claimed as a new theorem. Lean certifies correctness, not
--   priority.
--
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
theorem diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
        ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
