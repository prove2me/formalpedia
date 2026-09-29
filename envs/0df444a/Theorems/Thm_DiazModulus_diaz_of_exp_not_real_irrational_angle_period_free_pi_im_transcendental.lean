-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_free_pi_im_transcendental
-- name    : DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_transcendental
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T12:13:35.23267+00:00
-- url     : https://prove2.me/theorems/693914d7-8d52-4eb7-bc0b-e49d1985a621
-- title:
--   Irrational angle, $\pi\,\Im u\notin\overline{\mathbb Q}+\pi^{2}\mathbb Q$: the residual
-- statement:
--   **The complementary half** of the split of
--   `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free` described on
--   `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic`. The last
--   hypothesis here, `Transcendental ℚ ((Real.pi * u.im : ℝ) : ℂ)`, is by definition the negation of the
--   sibling's, so the reduction to the parent is a `by_cases` and carries no mathematical content.
--
--   **The hypothesis, read positively.** Combining the last two clauses:
--   $$\pi\,\Im u\ \notin\ \overline{\mathbb Q}+\pi^{2}\mathbb Q,$$
--   where — and this is the point of the node — the rational coefficient now ranges over **all** of
--   $\mathbb Q$, zero included. The parent `..._period_free` states that exclusion only for
--   $r\neq0$, and therefore still contains the degenerate slice $\pi\,\Im u\in\overline{\mathbb Q}$, on
--   which the mission's route to $1/\pi$ does fire (see the sibling node). **This node is the residual of
--   the irrational-angle leaf; its parent was not.**
--
--   **Witness — the honesty check.** $u_B=\sqrt{15}+i$, the parent's own witness. Then $|u_B|=4$,
--   $\Im u_B=1\notin\pi\mathbb Q$, $\Re u_B\neq0$, $e^{u_B}\notin\mathbb R$, $\pi(1+r\pi)$ is
--   transcendental for every $r\in\mathbb Q^{\times}$, and $\pi\,\Im u_B=\pi$ is transcendental. All
--   seven clauses machine-checked and `sorry`-free, from `Transcendental ℚ π` as an explicit hypothesis.
--
--   **What this half loses.** Everything the route on the sibling consumes. Under
--   $\pi\,\Im u\notin\overline{\mathbb Q}+\pi^{2}\mathbb Q$ the number $\nu=i(\Im u+r\pi)$ has
--   $(i\pi)\nu\notin\overline{\mathbb Q}$ for **every** rational $r$, so there is no second certified
--   product to put beside $u\bar u$: a candidate's certificate data is again the three-dimensional
--   $\operatorname{span}_{\overline{\mathbb Q}}\{1,u,\bar u\}$ with the single product $u\bar u$, which
--   `DiazModulus.sixExponentials_cannot_refute_candidate` already shows no six-exponentials-family
--   theorem can use. `Diaz.fibre_at_most_two` and `Diaz.nonreal_two_point_fibre_pi_sq` are vacuous here,
--   the exponential fibre of every rational multiple of $u$ meeting the algebraic-modulus locus in one
--   point only.
--
--   **Weaker, or the same problem again?** Weaker than the parent as a quantifier shape, and **not
--   closable**; neither is the sibling. This split reduces nothing. Its content is that the leaf's
--   three-way decomposition
--   $$\text{irrational-angle leaf}\;=\;\text{period-aligned}\ \sqcup\ \{\pi\,\Im u\in\overline{\mathbb Q}\}\ \sqcup\ \text{this node}$$
--   has its first two parts inside the basin of a single statement about $1/\pi$
--   ($\gamma/(i\pi)\notin\mathcal L$ for $\gamma\in\overline{\mathbb Q}^{\times}$) and its third outside
--   it. The predicate is invariant under the rational-scaling action $u\mapsto qu$, $q\in\mathbb
--   Q^{\times}$ (machine-checked), so the collapse mechanism (`Diaz.locus_stable`) that makes the
--   integer-indexed version of this family of splits equivalent to its parent does not apply. No claim of
--   strict weakening in provability is made, and neither child is known to imply the other.
--
--   **Novelty.** Elementary. Novelty is not asserted.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   **This branch is circular, and that is the important thing to know before spending time on it.** The single open leaf beneath this node is `DiazModulus.normSq_transcendental_of_generic_conj_pair`, which lies below `DiazModulus.norm_transcendental_of_generic_conj_pair`, and that node — together with Hermite–Lindemann, which this mission has Proved — implies the root `DiazModulus.diaz_modulus_conjecture`, with the converse also holding. So it is equivalent to the whole conjecture. Every refinement between here and there leaves the difficulty exactly where it started. Descending this branch does not lead to an easier problem.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real_irrational_angle_period_free_pi_im_transcendental :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      Transcendental ℚ ((Real.pi * u.im : ℝ) : ℂ) →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
