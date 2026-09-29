-- Prove2me | Theorems.Thm_DiazModulus_ringHom_preserves_linearIndependent
-- name    : DiazModulus.ringHom_preserves_linearIndependent
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:18:03.700049+00:00
-- url     : https://prove2.me/theorems/158e34f1-5f59-4fbb-9bd1-2247d24b9e5a
-- title:
--   A ring hom fixing the algebraic numbers preserves independence both ways
-- statement:
--   **A ring homomorphism fixing the algebraic numbers preserves $\overline{\mathbb{Q}}$-linear
--   independence, in both directions.**
--
--   Let $\Phi : \mathbb{C} \to \mathbb{C}$ be a ring homomorphism with $\Phi(a) = a$ for
--   every algebraic $a$, and let $x_1,\dots,x_n$ be complex. Then $x$ is
--   $\overline{\mathbb{Q}}$-linearly independent if and only if
--   $\Phi x_1,\dots,\Phi x_n$ is.
--
--   **Why this is the interesting statement and not a triviality.** One direction is routine.
--   The other uses that a ring homomorphism out of a field is injective — its kernel is an
--   ideal of $\mathbb{C}$ and $\Phi(1) = 1$ — so a relation downstream pulls back. Both
--   directions matter for the use below; only having one would be useless.
--
--   **What it is for.** This mission carries a transfer principle: for a hypothetical
--   counterexample $u$ to Diaz's conjecture there is a ring homomorphism $\Phi$ fixing
--   $\overline{\mathbb{Q}}$, sending $u$ to an *ordinary* point $t = r e^{i}$ of the same
--   circle, and commuting with conjugation on $\overline{\mathbb{Q}}(u)$
--   (`Diaz.candidate_indistinguishable`). Independence being preserved exactly is the step
--   that lets one carry a configuration at $u$ over to $t$: together with
--   $\Phi(\bar u) = \overline{\Phi(u)}$ it gives
--   $$\Phi\bigl(\operatorname{span}_{\overline{\mathbb{Q}}}\{1, u, \bar u\}\bigr)
--   \subseteq \operatorname{span}_{\overline{\mathbb{Q}}}\{1, t, \bar t\},$$
--   so a six-exponentials template at a counterexample would produce one at $t$.
--
--   **A relationship worth recording precisely.** This does *not* make the mission's
--   `DiazModulus.sixExponentials_cannot_refute_candidate` a corollary of the transfer
--   principle, and the reverse does not hold either. That node's no-go clause is stated for
--   **every** complex $u$, with no hypothesis of being a counterexample, so it cannot follow
--   from a statement quantified over counterexamples alone; its proof is a dimension count
--   that never uses the hypothesis. What this lemma establishes is that the two results
--   *compose*: transfer would reduce the no-go from all counterexamples to the single explicit
--   point $r e^{i}$ — a genuine reduction, made redundant by the no-go already holding
--   unconditionally.
--
--   The two are independent results about the same phenomenon. The transfer principle is
--   broader in reach, ruling out every vanishing statement with algebraic coefficients over
--   $\overline{\mathbb{Q}}(u)$; the no-go is quantitative, giving the threshold
--   $\dim = 3$ that explains why the strong four exponentials conjecture suffices where
--   ordinary six exponentials does not.
--
--   **Attribution.** The transfer principle is the mission author's, from notes predating this
--   mission. No novelty is claimed for the lemma below, which is elementary.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem ringHom_preserves_linearIndependent {n : ℕ} (Φ : ℂ →+* ℂ)
    (hfix : ∀ a : ↥Qbar, Φ (a : ℂ) = (a : ℂ)) (x : Fin n → ℂ) :
    LinearIndependent (↥Qbar) x ↔ LinearIndependent (↥Qbar) (fun i => Φ (x i)) := by
  sorry
end DiazModulus
