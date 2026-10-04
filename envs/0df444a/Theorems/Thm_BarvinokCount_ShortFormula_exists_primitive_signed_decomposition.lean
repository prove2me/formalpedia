-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_exists_primitive_signed_decomposition
-- name    : BarvinokCount.ShortFormula.exists_primitive_signed_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:29:56.196857+00:00
-- url     : https://prove2.me/theorems/446cc2a6-2726-41cc-a7f1-f5a716ad9273
-- title:
--   Theorem 5.4 (with the count of its proof) — K = Σ ε_i K_i over at most (2^d)^T primitive cones
-- statement:
--   Let $d\ge2$ and let $K=\operatorname{co}\{u_1,\dots,u_k\}\subseteq\mathbb{R}^d$ be a simple rational cone given by linearly independent generators $u_1,\dots,u_k\in\mathbb{Z}^d$. Let $T=T(d,\operatorname{Ind}K)$ be the smallest integer with
--   $$T\ge\frac{-\log\log1.9+\log\log(\operatorname{Ind}K)}{\log d-\log(d-1)}$$
--   ($T=0$ if $\operatorname{Ind}K=1$). Then there are $N\le(2^d)^T$ rational primitive cones $K_i=\operatorname{co}(g_i)$, each given by primitive generators $g_i$, and integers $\varepsilon_i$ such that
--   $$K=\sum_{i=1}^N\varepsilon_iK_i\quad(\text{as characteristic functions on }\mathbb{R}^d)\qquad\text{and}\qquad\sigma(K;c)=\sum_{i=1}^N\varepsilon_i\,\sigma(K_i;c)$$
--   for all $c\in\mathbb{R}^d$ which are regular points of $\sigma(K;\cdot)$ and of every $\sigma(K_i;\cdot)$.
--
--   Since $(2^d)^T$ is bounded by a polynomial in $\log\operatorname{Ind}K$ for fixed $d$, the decomposition is short; this is the core of the algorithm.
--
--   **Formalization Note** The printed theorem asserts a polynomial algorithm and does not state the count; the bound $N\le(2^d)^T$ is the count established in its proof (p. 777) and is stated here as part of the theorem. $d\ge2$ is required because $T$ involves $\log(d-1)$. The value $T=0$ for $\operatorname{Ind}K=1$ (where $\log\log1$ is undefined) is a convention giving the true bound $1$.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 777, Theorem 5.4; the count (2^d)^T from its proof, p. 777

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_sigma
import Definitions.Def_BarvinokCount_ShortFormula_iterCount

namespace BarvinokCount.ShortFormula

theorem exists_primitive_signed_decomposition {d k : ℕ} (hd : 2 ≤ d)
    (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    ∃ (N : ℕ) (m : Fin N → ℕ) (g : (i : Fin N) → Fin (m i) → Fin d → ℤ) (ε : Fin N → ℤ),
      N ≤ (2 ^ d) ^ iterCount d (coneIndex u) ∧
      (∀ i, IsPrimitiveGens (g i)) ∧
      IsSignedConeDecomp (cone u) g ε ∧
      ∀ c : Fin d → ℝ, IsRegular u c → (∀ i, IsRegular (g i) c) →
        sigma u c = ∑ i, (ε i : ℝ) * sigma (g i) c := by sorry

end BarvinokCount.ShortFormula
