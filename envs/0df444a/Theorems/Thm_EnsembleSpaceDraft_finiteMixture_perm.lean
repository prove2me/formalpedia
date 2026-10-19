-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_finiteMixture_perm
-- name    : EnsembleSpaceDraft.finiteMixture_perm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:48:22.821613+00:00
-- url     : https://prove2.me/theorems/60d29d4f-4d40-4d72-baea-9318ec478003
-- title:
--   Corollary 1.12 — finite mixtures are independent of order
-- statement:
--   Let $e_1,\ldots,e_n$ be ensembles in an ensemble space and let $p_1,\ldots,p_n$ be real coefficients with $0\le p_i\le 1$ and $\sum_{i=1}^n p_i=1$. For every permutation $\tau$ of $\{1,\ldots,n\}$ the finite mixture of Definition 1.10 exists, and
--   $$
--   \sum_{i=1}^n p_i e_i=\sum_{i=1}^n p_{\tau(i)} e_{\tau(i)}.
--   $$
--   The common value depends on the pairs $(p_i,e_i)$ only through the unordered collection of those pairs.
--
--   This is Corollary 1.12. The case $n=0$ does not arise: the sum of no coefficients is $0$, not $1$.
--
--   **Formalization Note.** Existence is part of the statement. The mixture is the partial operation of Definition 1.10, so the claim is that both orders return the same ensemble rather than that two possibly undefined expressions are equal as options.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Corollary 1.12, pp. 15–16.

import Definitions.Def_EnsembleSpaceDraft_finiteMixture
import Mathlib

open scoped BigOperators

namespace EnsembleSpaceDraft

universe u

/-- Corollary 1.12. A finite mixture does not depend on the order of the pairs.
Under the stated hypotheses the mixture exists, and every reordering returns the same ensemble. -/
theorem finiteMixture_perm {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E) {n : ℕ}
    (p : Fin n → ℝ) (e : Fin n → E) (τ : Equiv.Perm (Fin n))
    (hnn : ∀ i, 0 ≤ p i) (hle : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = 1) :
    ∃ m : E,
      finiteMixture X p e = some m ∧
        finiteMixture X (fun i => p (τ i)) (fun i => e (τ i)) = some m := by
  sorry

end EnsembleSpaceDraft
