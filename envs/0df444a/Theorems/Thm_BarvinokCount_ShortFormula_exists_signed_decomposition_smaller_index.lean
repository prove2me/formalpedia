-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_exists_signed_decomposition_smaller_index
-- name    : BarvinokCount.ShortFormula.exists_signed_decomposition_smaller_index
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:29:38.780991+00:00
-- url     : https://prove2.me/theorems/0eefb54a-a322-4e83-bb03-49294cebaeaf
-- title:
--   Lemma 5.3 — at most 2^d simple cones K_i with signs ±1, Ind K_i ≤ (Ind K)^{(d−1)/d}, K = Σ ε_i K_i and σ(K) = Σ ε_i σ(K_i)
-- statement:
--   Let $d\ge1$ and let $K=\operatorname{co}\{u_1,\dots,u_k\}\subseteq\mathbb{R}^d$ be a simple rational cone given by linearly independent generators $u_1,\dots,u_k\in\mathbb{Z}^d$. Then there are $N\le2^d$ simple rational cones $K_i=\operatorname{co}(g_i)$, each given by a list $g_i$ of linearly independent integral generators, and integers $\varepsilon_i\in\{-1,1\}$, $i=1,\dots,N$, such that
--
--   1. (a) $\operatorname{Ind}K_i\le(\operatorname{Ind}K)^{(d-1)/d}$ for all $i$;
--   2. (b) $K=\sum_i\varepsilon_iK_i$, i.e. $\chi_K(x)=\sum_i\varepsilon_i\chi_{K_i}(x)$ for all $x\in\mathbb{R}^d$, and
--   $$\sigma(K;c)=\sum_{i=1}^N\varepsilon_i\,\sigma(K_i;c)$$
--   for every $c\in\mathbb{R}^d$ that is a regular point of $\sigma(K;\cdot)$ and of every $\sigma(K_i;\cdot)$.
--
--   Iterating this lemma drives the index of every cone in the decomposition down to $1$.
--
--   **Formalization Note** The paper asserts a polynomial algorithm that constructs the cones; here their existence is stated. Part (c) of the printed lemma, "size $K_i\le$ size $K+O(d^2)$", has an unquantified constant and serves only the running-time bound; it is not stated. The hypothesis $d\ge1$ makes the exponent $(d-1)/d$ meaningful. The cones $K_i$ may have fewer generators than $K$ (they are faces of other cones); each is given by its own generator list.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 776, Lemma 5.3 (a), (b)

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_sigma

namespace BarvinokCount.ShortFormula

theorem exists_signed_decomposition_smaller_index {d k : ℕ} (hd : 1 ≤ d)
    (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    ∃ (N : ℕ) (m : Fin N → ℕ) (g : (i : Fin N) → Fin (m i) → Fin d → ℤ) (ε : Fin N → ℤ),
      N ≤ 2 ^ d ∧
      (∀ i, IsSimpleGens (g i)) ∧
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i, (coneIndex (g i) : ℝ) ≤ (coneIndex u : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))) ∧
      IsSignedConeDecomp (cone u) g ε ∧
      ∀ c : Fin d → ℝ, IsRegular u c → (∀ i, IsRegular (g i) c) →
        sigma u c = ∑ i, (ε i : ℝ) * sigma (g i) c := by sorry

end BarvinokCount.ShortFormula
