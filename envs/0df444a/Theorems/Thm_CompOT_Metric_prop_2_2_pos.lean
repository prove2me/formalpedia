-- Prove2me | Theorems.Thm_CompOT_Metric_prop_2_2_pos
-- name    : CompOT.Metric.prop_2_2_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:10.060878+00:00
-- url     : https://prove2.me/theorems/a4fb197a-bd52-4843-b496-799522d0dcca
-- title:
--   Proof of Proposition 2.2, pp. 377–378 — W_p(a, b) > 0 whenever a ≠ b
-- statement:
--   Let $D\in\mathbb R^{n\times n}_+$ be a distance on $[\![n]\!]$ (symmetric, $D_{i,j}=0\iff i=j$, triangle inequality), let $p\ge1$, and let $a,b\in\Sigma_n$ with $a\ne b$. Then
--   $$\mathrm W_p(a,b)>0.$$
--
--   Together with $\mathrm W_p(a,a)=0$ this is the definiteness of the Wasserstein distance: the off-diagonal entries of $D^p$ are positive, and every coupling of two distinct histograms puts mass off the diagonal.
--
--   **Formalization Note** $L_{D^p}(a,b)$ is a real infimum over $U(a,b)$; the strict inequality needs the infimum to be attained, which is a compactness fact to be proved, not a hypothesis.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.2, pp. 377–378

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- Proof of Proposition 2.2, pp. 377–378: by the positivity of all off-diagonal
elements of `D^p`, `W_p(a, b) > 0` whenever `a ≠ b`. -/
theorem prop_2_2_pos {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a b : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hab : a ≠ b) :
    0 < W D p a b := by sorry

end CompOT.Metric
