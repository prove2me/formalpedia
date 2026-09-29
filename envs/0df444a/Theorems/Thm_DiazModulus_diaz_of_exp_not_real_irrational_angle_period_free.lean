-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_free
-- name    : DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T10:38:38.28662+00:00
-- url     : https://prove2.me/theorems/5c573fdf-0df3-42af-9d7b-75e39a7c1f6b
-- title:
--   Irrational angle, period-free: every exponential fibre meets the locus once
-- statement:
--   **The complementary half** of the split of
--   `DiazModulus.diaz_of_exp_not_real_irrational_angle` described on
--   `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned`. The two extra hypotheses are
--   literally complementary; the reduction to the parent is a `by_cases`.
--
--   **The hypothesis, read positively.** $\pi\,\Im u\notin\overline{\mathbb Q}+\pi^{2}\mathbb Q$. It is
--   **local**: a membership statement about the single real number $\Im u$ in an explicit
--   $\overline{\mathbb Q}$-plane, not a negative existential over a large search space. Geometrically it
--   says that no non-zero rational multiple of $u$ has a second point of algebraic modulus in its
--   exponential fibre — every such fibre meets the algebraic-modulus locus in one point only.
--
--   **Witness — the honesty check.** $u_B=\sqrt{15}+i$. Then $|u_B|=4$, $\Im u_B=1\notin\pi\mathbb Q$,
--   $\Re u_B\neq0$, $e^{u_B}\notin\mathbb R$, and for every $r\in\mathbb Q^{\times}$ the number
--   $\pi(1+r\pi)=\pi+r\pi^{2}$ is transcendental, because $\pi$ is not a root of a non-zero rational
--   quadratic with algebraic constant term. Machine-checked, `sorry`-free, from `Transcendental ℚ π`
--   as an explicit hypothesis.
--
--   **What this half loses.** Everything the mission's fibre machinery consumes.
--   `Diaz.fibre_at_most_two` is vacuous here (the fibre already has a single point);
--   `Diaz.nonreal_two_point_fibre_pi_sq` has no hypothesis to feed on; and a candidate's certificate
--   data is again the three-dimensional $\operatorname{span}_{\overline{\mathbb Q}}\{1,u,\bar u\}$ with
--   the single certified product $u\bar u$, which
--   `DiazModulus.sixExponentials_cannot_refute_candidate` already shows no six-exponentials-family
--   theorem can use. So the difficulty of the leaf sits here, and the point of
--   publishing the pair is that the sibling is genuinely smaller rather than merely different.
--
--   **Weaker, or the same problem again?** Both children are weaker than the parent as quantifier
--   shapes, and **neither is known to imply the other**. That deserves an explicit remark. On this
--   mission the usual fate of a split is that the residual half is carried back onto the whole parent by
--   the rational-scaling action $u\mapsto qu$ (`Diaz.locus_stable`), and that is exactly what happens to
--   the naive version of this split in which $r$ is required to be an **integer**: from a counterexample
--   with integer witness $n$, scaling by a prime $p>|n|$ gives a counterexample with no integer witness,
--   so the integer-residual child is *equivalent* to the parent. The predicate used here is invariant
--   under that action (machine-checked), so that collapse does not occur. This is **not** a proof that
--   this child is strictly weaker in provability; no such proof is claimed. It says only that the one
--   mechanism which trivialises splits on this mission has been neutralised.
--
--   **Novelty.** Elementary. Novelty is not asserted.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   Open leaves beneath this node: `normSq_transcendental_of_generic_conj_pair`, `recip_pi_not_log_real_gamma`, `recip_pi_not_log_imag_gamma`. The first lies below `norm_transcendental_of_generic_conj_pair`, which is **equivalent to the root** modulo Hermite–Lindemann, so the part of this subtree that runs through it is circular. The others are genuine reductions.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real_irrational_angle_period_free :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
