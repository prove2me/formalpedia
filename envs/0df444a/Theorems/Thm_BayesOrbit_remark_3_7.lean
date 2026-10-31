-- Prove2me | Theorems.Thm_BayesOrbit_remark_3_7
-- name    : BayesOrbit.remark_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:33.517453+00:00
-- url     : https://prove2.me/theorems/67007600-8cba-4ef2-bcc2-19d62f2053c8
-- title:
--   Remark 3.7 — algebraically independent entries force integer relations to vanish (extended: adds $\det A\ne0$ and the instance $A\theta=\mathbf 1$ that Lemma 3.8 needs)
-- statement:
--   Let $I$ be a finite set and $A=(a_{ij})_{i,j\in I}$ a real matrix whose entries are algebraically independent over $\mathbb Q$. Then:
--
--   1. for each row $l$, an integer vector $r$ with $\sum_i a_{l,i}r_i\in\mathbb Z$ is zero;
--   2. $\det A\ne0$;
--   3. if $\theta\in\mathbb R^I$ satisfies $A\theta=\mathbf 1$, the all-ones vector, then an integer vector $w$ with $\sum_i w_i\theta_i\in\mathbb Z$ is zero.
--
--   Clause 1 is the remark as printed. Clause 3 is what makes the integrality condition of Kronecker's theorem hold for the single column $\theta$, which is the instance behind the one integer $d$ of Lemma 3.8.
--
--   Differences from the source:
--   - generalization: the vanishing clause for (3.10) alone → the printed vanishing clause, plus det A ≠ 0 and the vanishing of integer relations of θ with A θ = 1; reason: the printed remark is true and is clause 1, so the Lean implies it; the two added clauses are what the proof of Lemma 3.8 needs once Theorem 3.4 is corrected, since the printed clause then gives a row-dependent d_k
--   - reading: (3.10) with the index l free → for each row l separately; reason: the conclusion for a single row implies the one for all rows, so this is the stronger reading
-- source:
--   Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted manuscript (Enlighten 227272), Remark 3.7, eq. (3.10), p.16

import Mathlib

open scoped BigOperators

namespace BayesOrbit

/-- Remark 3.7 of Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted
manuscript (Enlighten 227272), p.16 (PDF 17), extended. For a square matrix `A` with algebraically
independent entries: (3.10), already for a single row `l`, forces `r = 0`, as printed; moreover
`det A ≠ 0`, and for `θ` with `A θ = 1` (the all-ones vector) an integer vector `w` with
`∑ i, w i * θ i ∈ ℤ` is `0`.

**Formalization Note.** Algebraic independence is over `ℚ`, of the family indexed by `I × I`. The
index `l` is free in the printed (3.10); the first clause holds for each row, so it covers the
reading "for all `l`" as well. The other two clauses are the instance of the integrality condition
of `theorem_3_4` that the proof of Lemma 3.8 needs in place of the printed clause: `θ` as a single
column, which is what yields one integer `d` common to all rows. -/
theorem remark_3_7 {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℝ)
    (hA : AlgebraicIndependent ℚ (fun x : I × I => A x.1 x.2)) :
    (∀ (l : I) (r : I → ℤ), (∃ z : ℤ, ∑ i, A l i * (r i : ℝ) = (z : ℝ)) → r = 0) ∧
    A.det ≠ 0 ∧
    ∀ θ : I → ℝ, A.mulVec θ = 1 →
      ∀ w : I → ℤ, (∃ z : ℤ, ∑ i, (w i : ℝ) * θ i = (z : ℝ)) → w = 0 := by sorry

end BayesOrbit
