-- Prove2me | Theorems.Thm_CompOT_Metric_prop_2_2_minkowski
-- name    : CompOT.Metric.prop_2_2_minkowski
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:15.088187+00:00
-- url     : https://prove2.me/theorems/cdac5799-b7ac-4298-991e-fd05be8f4207
-- title:
--   Proof of Proposition 2.2, pp. 378–379 — ⟨S, D^p⟩^{1/p} ≤ ⟨P, D^p⟩^{1/p} + ⟨Q, D^p⟩^{1/p} for the glued S
-- statement:
--   Let $D\in\mathbb R^{n\times n}_+$ be a distance on $[\![n]\!]$, $p\ge1$, $a,b,c\in\Sigma_n$, $P\in U(a,b)$, $Q\in U(b,c)$, and let $S=P\,\mathrm{diag}(1/\tilde b)\,Q$ be the glued coupling. Then
--   $$\langle S,D^p\rangle^{1/p}\le\langle P,D^p\rangle^{1/p}+\langle Q,D^p\rangle^{1/p}.$$
--
--   This is the chain of inequalities of pp. 378–379 (the triangle inequality of $D$ followed by Minkowski's inequality), together with its final identities $\sum_{ijk}D^p_{ij}P_{ij}Q_{jk}/\tilde b_j=\langle P,D^p\rangle$ and $\sum_{ijk}D^p_{jk}P_{ij}Q_{jk}/\tilde b_j=\langle Q,D^p\rangle$. With the gluing lemma and the suboptimality of $S$ it yields the triangle inequality for $\mathrm W_p$ once $P$ and $Q$ are optimal.
--
--   **Formalization Note** The page applies the chain to optimal $P$ and $Q$; the inequality does not use optimality and is stated for all couplings. The page's two final equalities are folded into the right-hand side.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.2, pp. 378–379

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- Proof of Proposition 2.2, pp. 378–379 (the chain after "The triangle inequality
follows then from", with its two final equalities): for `P ∈ U(a, b)`, `Q ∈ U(b, c)` and
`S = P diag(1/b̃) Q`, `⟨S, D^p⟩^{1/p} ≤ ⟨P, D^p⟩^{1/p} + ⟨Q, D^p⟩^{1/p}`. -/
theorem prop_2_2_minkowski {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a b c : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hc : c ∈ stdSimplex ℝ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b) (hQ : Q ∈ CompOT.Assignment.couplings b c) :
    CompOT.Assignment.frob (powCost D p) (glue b P Q) ^ (1 / p) ≤
      CompOT.Assignment.frob (powCost D p) P ^ (1 / p) + CompOT.Assignment.frob (powCost D p) Q ^ (1 / p) := by sorry

end CompOT.Metric
