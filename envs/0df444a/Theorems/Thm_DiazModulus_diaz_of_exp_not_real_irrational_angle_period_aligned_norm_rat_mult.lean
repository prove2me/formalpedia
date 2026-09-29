-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
-- name    : DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T14:23:19.191378+00:00
-- url     : https://prove2.me/theorems/561efd5c-2eb5-4258-a55b-a7c035576bac
-- title:
--   Period-aligned, norm a rational multiple of the aligned datum: the four-exponentials-reachable half
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
--   **Why this is the right cut.** Under a counterexample $\alpha=e^{u}\in\overline{\mathbb Q}$
--   the four numbers
--   $$u,\qquad \nu,\qquad c\cdot 2\pi i\ (c\in\mathbb Q^{\times}),\qquad \bar u$$
--   all lie in $\mathcal L$ ($e^{\bar u}=\bar\alpha$; $e^{2\pi i}=1$; and
--   $e^{2d\nu}=(\alpha/\bar\alpha)^{d}$ for $d$ the denominator of $r$, so $\nu\in\mathcal L$
--   because $\mathcal L$ is a $\mathbb Q$-vector space). Form
--   $$M=\begin{pmatrix}u&\nu\\ c\,2\pi i&\bar u\end{pmatrix},\qquad
--   \det M=u\bar u-c\,\nu\cdot 2\pi i=A+2c\beta .$$
--   On this half choose $c=-A/(2\beta)\in\mathbb Q^{\times}$, so $\det M=0$. The rows are
--   $\mathbb Q$-independent because $\Re u\neq0$; the columns are $\mathbb Q$-independent because
--   $\Re u\neq0$ and $\nu\neq0$ — and those two facts are *exactly* the parent's hypotheses
--   $\Re u\neq0$ and $\theta\notin\pi\mathbb Q$. So this half follows from the **four
--   exponentials conjecture** (determinant form: a $2\times2$ matrix over $\mathcal L$ with
--   $\mathbb Q$-independent rows and columns has non-zero determinant).
--
--   That is a real gain: `DiazModulus.recip_pi_log_of_period_aligned` reduces the *whole* aligned
--   leaf to a statement needing the **strong** four exponentials conjecture, and $4EC$ is strictly
--   weaker than $SFEC$.
--
--   **And here the configuration is in the regime where $4EC$ is known.** Eliminating
--   $\theta=\beta/\pi-r\pi$ from $t^{2}+\theta^{2}=A$ gives
--   $$t^{2}\pi^{2}+r^{2}\pi^{4}-(A+2r\beta)\pi^{2}+\beta^{2}=0,$$
--   a non-trivial polynomial relation over $\overline{\mathbb Q}$ between $t$ and $\pi$. Hence $t$
--   is algebraic over $\overline{\mathbb Q}(\pi)$ and
--   $$\operatorname{trdeg}_{\mathbb Q}\mathbb Q(u,\bar u,\nu,2\pi i)=1 .$$
--   `Diaz.four_exp_trdeg_one` — the mission's port of Roy–Waldschmidt 1995, Theorem 1 — is
--   precisely $4EC$ in transcendence degree $\le 1$, and its conclusion is the row/column
--   dichotomy refuted above. **So this node should be closable from `Diaz.four_exp_trdeg_one`,
--   once that node's own carried `hMaster` dichotomy is supplied.** It was closed instead from `DiazModulus.four_exponentials_trdeg_one`, the unconditional form for logarithms of algebraic numbers, once that node was proved.
--
--   Note that the transcendence-degree-one property holds on the *whole* aligned class, and fails
--   on the period-free half, where $\theta$ ranges over an uncountable set and
--   $\operatorname{trdeg}_{\mathbb Q}\mathbb Q(t,\theta,\pi)=2$. That, and not the shape of the
--   predicate, is the real content of the aligned/free split.
--
--   **Witness — the honesty check.** With $\theta_A=1/\pi-\pi$ and
--   $u_A=\sqrt{16-\theta_A^{2}}+i\theta_A$ one has $r=1$, $\beta=\pi(\theta_A+\pi)=1$, $A=16$, so
--   $A=16\cdot\beta$ and $u_A$ satisfies every hypothesis of this node. Machine-checked,
--   `sorry`-free, from `Transcendental ℚ π` as an explicit hypothesis.
--
--   **Hypotheses that are not load-bearing.** The route above uses only $\Re u\neq0$,
--   $\theta\notin\pi\mathbb Q$ and the rational-multiple relation. `u ≠ 0`, `‖u‖` algebraic and
--   `(exp u).im ≠ 0` are carried only so that the two children sum to the parent. (On this branch
--   `(exp u).im ≠ 0` is in any case implied by $\theta\notin\pi\mathbb Q$.)
--
--   **Novelty.** Elementary given the four exponentials literature; the only observation is which
--   $2\times2$ determinant the two certified products $u\bar u\in\overline{\mathbb Q}$ and
--   $\nu\cdot2\pi i\in\overline{\mathbb Q}^{\times}$ can be made to fill. Not found in the sources
--   consulted; no literature search was performed in this run. Lean certifies correctness, not
--   priority.
--
--
--   ---
--
--   **Status on the graph.**
--   This node is now **Proved**: it closed when its last open leaf, `four_exponentials_trdeg_one`, was proved.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
        ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
