-- Prove2me | Theorems.Thm_CompOT_Metric_prop_2_2_symm
-- name    : CompOT.Metric.prop_2_2_symm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:06.268439+00:00
-- url     : https://prove2.me/theorems/3283911d-16a5-4afb-8366-b3550bd6064c
-- title:
--   Proof of Proposition 2.2, p. 378 — by symmetry of D^p, W_p(a, b) = W_p(b, a)
-- statement:
--   Let $D\in\mathbb R^{n\times n}_+$ be a distance on $[\![n]\!]$, let $p\ge1$ and $a,b\in\Sigma_n$. Then
--   $$\mathrm W_p(a,b)=\mathrm W_p(b,a).$$
--
--   The page derives this from the symmetry of $D^p$; it rests on the remark of p. 371 that $P\in U(a,b)$ if and only if $P^{\top}\in U(b,a)$.
--
--   **Formalization Note** Indices are `Fin n`; all hypotheses of Proposition 2.2 are kept.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.2, p. 378; symmetry of U(a, b) under transposition, p. 371

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- Proof of Proposition 2.2, p. 378: by symmetry of `D^p`, `W_p(a, b)` is itself a
symmetric function. -/
theorem prop_2_2_symm {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a b : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) :
    W D p a b = W D p b a := by sorry

end CompOT.Metric
