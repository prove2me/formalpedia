-- Prove2me | Theorems.Thm_CompOT_Metric_prop_2_2_diag
-- name    : CompOT.Metric.prop_2_2_diag
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:04.636598+00:00
-- url     : https://prove2.me/theorems/4245da35-2670-4ace-955a-094facb9d4bf
-- title:
--   Proof of Proposition 2.2, p. 377 — diag(a) is an optimal coupling of a with itself and W_p(a, a) = 0
-- statement:
--   Let $D\in\mathbb R^{n\times n}_+$ be a distance on $[\![n]\!]$: symmetric, $D_{i,j}=0$ if and only if $i=j$, and $D_{i,k}\le D_{i,j}+D_{j,k}$ for all $i,j,k$. Let $p\ge 1$ and $a\in\Sigma_n$. Then the diagonal matrix $\mathrm{diag}(a)$ is an optimal coupling in $U(a,a)$ for the cost $D^p$, its cost $\langle D^p,\mathrm{diag}(a)\rangle$ is zero, and
--   $$\mathrm W_p(a,a)=0.$$
--
--   This is the first step of the definiteness part of Proposition 2.2: because $D^p$ has a null diagonal, the mass of $a$ can stay in place at no cost.
--
--   **Formalization Note** Indices are `Fin n`. The hypotheses (i)–(iii) of Proposition 2.2 and $D\ge 0$, $p\ge1$ are carried even where the step uses only part of them, so all items share one setting.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.2, p. 377

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- Proof of Proposition 2.2, p. 377: since `D^p` has a null diagonal, `W_p(a, a) = 0`,
with corresponding optimal transport matrix `P⋆ = diag(a)`. -/
theorem prop_2_2_diag {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) :
    CompOT.Assignment.IsOptimalCoupling (powCost D p) a a (Matrix.diagonal a) ∧
      CompOT.Assignment.frob (powCost D p) (Matrix.diagonal a) = 0 ∧
      W D p a a = 0 := by sorry

end CompOT.Metric
