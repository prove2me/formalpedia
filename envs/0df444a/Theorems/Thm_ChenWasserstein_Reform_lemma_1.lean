-- Prove2me | Theorems.Thm_ChenWasserstein_Reform_lemma_1
-- name    : ChenWasserstein.Reform.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:09.85347+00:00
-- url     : https://prove2.me/theorems/3f34205e-8a36-48a9-b600-43578437a401
-- title:
--   Lemma 1 — attained LP representation of a fractional sorted sum
-- statement:
--   Let $N\ge1$, let $k_1,\ldots,k_N$ be arbitrary real numbers, and let $0<\varepsilon<1$. Let $F_k(\varepsilon N)$ denote the fractional sum of the $\varepsilon N$ smallest entries, counting ties with multiplicity. Then the following maximum is attained and equals that sum:
--   $$F_k(\varepsilon N)=\max\left\{\varepsilon Nt-\sum_{i=1}^N s_i:\ t\in\mathbb R,\ s_i\ge0,\ t-s_i\le k_i\ (1\le i\le N)\right\}.$$
--   In particular, there exist feasible $s,t$ achieving the displayed value, and every feasible $s',t'$ has objective at most that value.
--
--   This finite linear-program representation applies to arbitrary real arrays, and supplies the scalar threshold and slack variables in the deterministic chance-constraint reformulation.
--
--   **Formalization Note** No nonnegativity assumption is made on $k_i$, and $t$ is free. The maximum is expressed by an attaining pair and a universal upper bound, avoiding an unguarded real supremum. The fractional next entry is included when needed, including when $\varepsilon N<1$, and is not rounded away.
-- source:
--   Chen, Kuhn and Wiesemann, Technical Note—Data-Driven Chance Constrained Programs over Wasserstein Balls, Operations Research 72(1) (2024), 410–424, https://doi.org/10.1287/opre.2022.2330, Lemma 1, printed pp. 415–416, PDF pp. 6–7

import Mathlib
import Definitions.Def_ChenWasserstein_Reform_Data

open scoped BigOperators

/- Imported declaration bodies, quoted verbatim for standalone blind auditing.
These are comments, not redeclarations or additional assumptions.

noncomputable def kthSmallest {N : ℕ} (v : Fin N → ℝ) (j : ℕ) : ℝ :=
  ((Finset.univ.val.map v).sort (· ≤ ·)).getD j 0

noncomputable def fractionalSmallest {N : ℕ} (k : Fin N → ℝ) (ℓ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (min ⌊ℓ⌋₊ N), WassDRCCP.Improved.kthSmallest k j) +
    if ⌊ℓ⌋₊ < N then
      (ℓ - (⌊ℓ⌋₊ : ℝ)) * WassDRCCP.Improved.kthSmallest k ⌊ℓ⌋₊ else 0
-/

namespace ChenWasserstein.Reform

/-- Chen, Kuhn and Wiesemann (2024), Lemma 1, printed pp. 415–416 / PDF pp. 6–7.
The maximum is attained, and k may have negative entries. -/
theorem lemma_1 {N : ℕ} (k : Fin N → ℝ) (ε : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (s : Fin N → ℝ) (t : ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i, t - s i ≤ k i) ∧
      ε * (N : ℝ) * t - ∑ i, s i = fractionalSmallest k (ε * (N : ℝ)) ∧
      ∀ (s' : Fin N → ℝ) (t' : ℝ),
        (∀ i, 0 ≤ s' i) → (∀ i, t' - s' i ≤ k i) →
        ε * (N : ℝ) * t' - ∑ i, s' i ≤ fractionalSmallest k (ε * (N : ℝ)) := by sorry

end ChenWasserstein.Reform
