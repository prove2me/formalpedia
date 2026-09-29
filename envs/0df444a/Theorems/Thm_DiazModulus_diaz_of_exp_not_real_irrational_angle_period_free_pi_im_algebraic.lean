-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic
-- name    : DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T12:13:36.915058+00:00
-- url     : https://prove2.me/theorems/c6b3a67d-4354-4d2e-9893-f35a5fc8cea2
-- title:
--   Irrational angle, no period translate but $\pi\,\Im u$ algebraic
-- statement:
--   **One half of an ambient-space split of `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free`.**
--   The sibling half is `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_transcendental`;
--   the two last hypotheses are literally complementary (`Transcendental ℚ x` is by definition
--   `¬ IsAlgebraic ℚ x`), so the reduction to the parent is a `by_cases` and carries no mathematical
--   content.
--
--   **Why this predicate exists — a gap in the generation above.** The split of
--   `DiazModulus.diaz_of_exp_not_real_irrational_angle` used
--   $$\mathrm{PeriodAligned}\ u\ :\Longleftrightarrow\ \exists\, r\in\mathbb Q^{\times}:\ \pi(\Im u+r\pi)\in\overline{\mathbb Q},$$
--   and the clause $r\neq0$ is there for the *geometric* reading only: writing $r=n/q$, the translate
--   index $n$ must be non-zero for $qu+2\pi i n$ to be a **second** point of the exponential fibre. It is
--   not needed for the arithmetic. The published route lemma
--   `DiazModulus.recip_pi_log_of_period_aligned` carries $r\neq0$ but **never uses it** — the same proof
--   goes through verbatim with $r$ ranging over all of $\mathbb Q$. So the degenerate case $r=0$, namely
--   $$\pi\,\Im u\in\overline{\mathbb Q},$$
--   was left on the *period-free* side of that split although it behaves exactly like the period-aligned
--   side. This node is that case.
--
--   **What it reduces to.** Put $\nu=\tfrac12(u-\bar u)=i\,\Im u$. Then $e^{2\nu}=e^{u}/\overline{e^{u}}$
--   is algebraic whenever $e^{u}$ is, so $\nu\in\mathcal L$; $\nu\neq0$ because $\Im u\notin\pi\mathbb Q$;
--   and $(i\pi)\nu=-\pi\,\Im u\in\overline{\mathbb Q}^{\times}$ by the last hypothesis. Hence
--   $\nu=\gamma/(i\pi)$ with $\gamma=-\pi\,\Im u$ algebraic and non-zero, and this child follows from
--   $$\gamma/(i\pi)\notin\mathcal L\quad\text{for every }\gamma\in\overline{\mathbb Q}^{\times},$$
--   which is exactly what the period-aligned sibling reduces to — a statement about $1/\pi$ alone,
--   implied by the strong four exponentials conjecture, open, and far more special than the leaf. **No
--   period translate is involved here**, so the route is shorter than on the aligned side: $\nu$ is
--   literally half of $u-\bar u$.
--
--   **Disjointness, and what the two halves are together.** Given the transcendence of $\pi$
--   (`DiazModulus.pi_transcendental`), $\pi\,\Im u\in\overline{\mathbb Q}$ and
--   $\mathrm{PeriodAligned}\,u$ are **mutually exclusive** — their difference is $r\pi^{2}$ with
--   $r\in\mathbb Q^{\times}$. Their union is the saturated region
--   $\exists\,r\in\mathbb Q:\ \pi(\Im u+r\pi)\in\overline{\mathbb Q}$. So
--   `..._period_aligned` together with this node are exactly the part of the irrational-angle leaf that
--   the displayed statement about $1/\pi$ settles, and the sibling
--   `..._period_free_pi_im_transcendental` is what is left over.
--
--   **A redundant hypothesis, flagged.** The sixth hypothesis — no $r\in\mathbb Q^{\times}$ with
--   $\pi(\Im u+r\pi)\in\overline{\mathbb Q}$ — is **implied** by the seventh together with the
--   transcendence of $\pi^{2}$; it is carried only so that the two children sum to the parent. The
--   clauses $u\neq0$, $|u|$ algebraic, $e^{u}\notin\mathbb R$ and the off-axes clause are likewise
--   unused by the route above and carried for the same reason.
--
--   **Witness — the honesty check.** Both halves of the split are non-empty. A member of this one:
--   $$u_C=\sqrt{16-\pi^{-2}}+\frac{i}{\pi}=3.9873147375593091\ldots+0.3183098861837906\ldots\,i .$$
--   Then $|u_C|=4$, $\pi\,\Im u_C=1$, $\Im u_C\notin\pi\mathbb Q$, $\Re u_C\neq0$,
--   $e^{u_C}\notin\mathbb R$, and for every $r\in\mathbb Q^{\times}$ the number
--   $\pi(\Im u_C+r\pi)=1+r\pi^{2}$ is transcendental. All seven clauses machine-checked and
--   `sorry`-free, from `Transcendental ℚ π` as an explicit hypothesis, nothing imported.
--
--   **Easier, or only weaker?** **Weaker**, as a quantifier shape, and **not closable** — neither half
--   of this split is, and that is said plainly rather than hidden. The value of the split is *location*,
--   not reduction: it moves a slice out of the node that was presented as the leaf's residual and into
--   the basin of the $1/\pi$ statement above. The predicate is invariant under the rational-scaling
--   action $u\mapsto qu$, $q\in\mathbb Q^{\times}$ (machine-checked), so the mechanism that trivialises
--   splits on this mission (`Diaz.locus_stable`) does not apply here; that is not a proof of strict
--   weakening, and none is claimed.
--
--   **Novelty.** Elementary. Novelty is not asserted. Lean certifies correctness, not priority.
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
theorem diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ) →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
