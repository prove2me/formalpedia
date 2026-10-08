-- Prove2me | Theorems.Thm_CompOT_Metric_proposition_2_2
-- name    : CompOT.Metric.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:09.412583+00:00
-- url     : https://prove2.me/theorems/9d3af7fb-43bd-4a8e-9fed-4b3bf94dbcd1
-- title:
--   Proposition 2.2, p. 377 — for a distance matrix D and p ≥ 1, W_p = L_{D^p}^{1/p} is a distance on Σ_n
-- statement:
--   Let $p\ge1$ and let $D\in\mathbb R^{n\times n}_+$ be a distance on $[\![n]\!]$, i.e.
--
--   1. $D$ is symmetric;
--   2. $D_{i,j}=0$ if and only if $i=j$;
--   3. $D_{i,k}\le D_{i,j}+D_{j,k}$ for all $(i,j,k)\in[\![n]\!]^3$.
--
--   For histograms $a,b\in\Sigma_n$ let $\mathrm W_p(a,b)=L_{D^p}(a,b)^{1/p}$, where $L_{D^p}(a,b)=\min_{P\in U(a,b)}\sum_{i,j}D_{i,j}^pP_{i,j}$ is the optimal transport cost for the entrywise power $D^p$. Then $\mathrm W_p$ is a distance on $\Sigma_n$: for all $a,b,c\in\Sigma_n$,
--   $$\mathrm W_p(a,b)=\mathrm W_p(b,a),\qquad \mathrm W_p(a,b)\ge0,\qquad \mathrm W_p(a,b)=0\iff a=b,\qquad \mathrm W_p(a,c)\le\mathrm W_p(a,b)+\mathrm W_p(b,c).$$
--
--   Optimal transport thus lifts a ground distance on bins to a distance between histograms on those bins, the $p$-Wasserstein distance.
--
--   **Formalization Note** Indices are `Fin n` (0-based); $\Sigma_n$ is Mathlib's `stdSimplex ℝ (Fin n)`. The book's "positive" is read as nonnegativity; strict positivity for $a\ne b$ is the clause $\mathrm W_p(a,b)=0\iff a=b$. The minimum is written as a real infimum over $U(a,b)$, which is nonempty and compact for $a,b\in\Sigma_n$. Powers are real powers with $p\in\mathbb R$, $p\ge1$. The book's $D\in\mathbb R^{n\times n}_+$ is the hypothesis $D_{i,j}\ge0$. For $n=0$ the simplex is empty and the statement holds vacuously, as in the book.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 2.2 and (2.17), p. 377

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- **Proposition 2.2** (p. 377). Let `D ∈ ℝ₊^{n×n}` be a distance on `⟦n⟧` (symmetric,
`D_{i,j} = 0 ↔ i = j`, triangle inequality) and `p ≥ 1`. Then `W_p(a, b) = L_{D^p}(a, b)^{1/p}`
(2.17) is a distance on `Σ_n`: symmetric, nonnegative, `W_p(a, b) = 0 ↔ a = b`, and it satisfies
the triangle inequality. -/
theorem proposition_2_2 {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k) :
    ∀ a ∈ stdSimplex ℝ (Fin n), ∀ b ∈ stdSimplex ℝ (Fin n), ∀ c ∈ stdSimplex ℝ (Fin n),
      W D p a b = W D p b a ∧
      0 ≤ W D p a b ∧
      (W D p a b = 0 ↔ a = b) ∧
      W D p a c ≤ W D p a b + W D p b c := by sorry

end CompOT.Metric
