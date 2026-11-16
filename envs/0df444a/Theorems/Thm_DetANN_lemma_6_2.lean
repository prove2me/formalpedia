-- Prove2me | Theorems.Thm_DetANN_lemma_6_2
-- name    : DetANN.lemma_6_2
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T17:41:21.676486+00:00
-- url     : https://prove2.me/theorems/4c0d47b0-707a-4c12-b51a-0c3113e3ee58
-- title:
--   Lemma 6.2: the conditional expectation of the potential
-- statement:
--   Let $d,L\ge1$, let $h$ be a real $d\times d$ matrix, $\tau\in\mathbb R$, $p_0\in\mathbb N$ and $\mathcal D\subseteq\mathbb R^d$ finite, and let $\Phi$ be the potential (24) of the signed blocks built from $h$. For every partial assignment $(\mu,u)$ of the $Ld$ signs,
--
--   $$\mathbb E\bigl[\Phi\ \big|\ (\mu,u)\bigr]=\text{the Lemma 6.2 expression at }(\mu,u),$$
--
--   where the left side is the average of $\Phi$ over all completions and the right side is the explicit generating-function formula of the definition `DetANN_SignChoice`.
--
--   The right side is a finite combination of truncated polynomial products, which is what the algorithm evaluates. So this is the statement that the deterministic sign selection computes the conditional expectation exactly.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Lemma 6.2 and its proof, pp.15–16

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_SignChoice

namespace DetANN

/-- **Lemma 6.2.** For every partial assignment `(μ, u)` of the `Ld` signs, the conditional
expectation of the potential `Φ` of (24) equals the explicit generating-function expression
`lemma62Expr`. -/
theorem lemma_6_2 {d : ℕ} (hd : 1 ≤ d) (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ) (hL : 1 ≤ L)
    (τ : ℝ) (p₀ : ℕ) (D : Finset (EuclideanSpace ℝ (Fin d))) (μ u : Fin L → Fin d → Bool) :
    condPotential h L τ p₀ D μ u = lemma62Expr h L τ p₀ D μ u := by sorry

end DetANN
