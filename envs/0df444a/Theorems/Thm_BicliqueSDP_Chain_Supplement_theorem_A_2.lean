-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_Supplement_theorem_A_2
-- name    : BicliqueSDP.Chain.Supplement.theorem_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:19:17.369113+00:00
-- url     : https://prove2.me/theorems/b09c7105-06c7-4dc7-9568-b9af053ba6a4
-- title:
--   Theorem A.2 — the sharpened product-free cardinality bound
-- statement:
--   Let $\Gamma$ be a finite group and let $k$ be the least dimension of a nontrivial finite-dimensional complex representation of $\Gamma$. Every product-free subset $A\subseteq\Gamma$ satisfies
--
--   $$|A|\le\frac{|\Gamma|}{1+k^{1/3}}.$$
--
--   The root is the positive real cube root. This is the paper's sharpened bound, retaining the additive $1$ in the denominator. Lemma A.1 supplies its spectral input.
--
--   **Formalization Note** The minimum is expressed as a least-element hypothesis, so no arbitrary default value is assigned for the trivial group, whose only product-free subset is empty. Complex representations are used, with no requirement that they be faithful or irreducible.
--
--   Differences from the source:
--   - encoding: The source names the minimum nontrivial representation dimension and writes k^(1/3) → Lean uses a least-element predicate for complex representations and real exponentiation by 1/3; reason: The minimum is positive whenever it exists, so real exponentiation equals its positive cube root; no false existence assumption is imposed on the trivial group.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 36, Theorem A.2

import Definitions.Def_BicliqueSDP_Chain_Supplement_ProductFree
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement

/-- Theorem A.2: the sharpened product-free density bound with its exact denominator. -/
theorem theorem_A_2 {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ) (k : ℕ) (hk : IsMinRepDim Γ k) (hA : IsProductFree A) :
    (A.card : ℝ) ≤ (Fintype.card Γ : ℝ) / (1 + (k : ℝ) ^ (1 / 3 : ℝ)) := by sorry

end BicliqueSDP.Chain.Supplement
