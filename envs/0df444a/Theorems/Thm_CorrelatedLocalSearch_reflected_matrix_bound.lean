-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_reflected_matrix_bound
-- name    : CorrelatedLocalSearch.reflected_matrix_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:22.645075+00:00
-- url     : https://prove2.me/theorems/ff1b8528-099f-44dc-89b7-af032e1c96ad
-- title:
--   Proof of Lemma C.1 — $R^{(m)}$ preserves increasing vectors, and $F_T(h)$ bounds paths below $m$
-- statement:
--   Let $k/2<r<k$, $m\ge2$, $L=m-1$, and let $R^{(m)}$ be the reflected comparison matrix on $\{1,\dots,L\}$.
--
--   1. If $f$ is nonnegative and nondecreasing on $\{1,\dots,L\}$, so is $R^{(m)}f$.
--   2. For every process satisfying the integer-potential hypotheses of Lemma C.1 with initial potential $h<m$ and every $T\ge0$,
--   $$
--   \sum_{\substack{|w|=T,\ w\text{ survives},\\ \mathrm{pot}(u)<m \text{ for every prefix } u \text{ of } w}} k^{-s_*T}\ \le\ F_T(h)=\bigl((R^{(m)})^T\mathbf 1\bigr)(h).
--   $$
--
--   This is the second part of the cover of $\{\tau>T\}$: the cost of the live paths that stay below the barrier.
--
--   **Formalization Note** Vectors on $\{1,\dots,L\}$ are functions on `Fin (m − 1)` with its order (index $i$ = potential $i+1$); $F_T$ is `reflF`. A word of length $T$ is `List.ofFn v`.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: a deterministic process with live histories, a potential and a stopping time τ → a liveness predicate `live` and a potential `pot` on words; a history is live in the paper's sense when all its prefixes satisfy `live` (`Surv`); τ = hitTime live ∈ ℕ∞, ⊤ if it never stops; reason: every deterministic process driven by the tape is described this way, and conversely
--   - reading: nonnegative increasing vectors → nonnegative nondecreasing vectors (Monotone); reason: F_0 = 1 is constant, so 'increasing' means nondecreasing
--   - encoding: L = m − 1 with a barrier m > h ≥ 1 → 2 ≤ m; reason: the paper's barrier has m ≥ 2; at m ≤ 1 the index set is empty
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess
import Definitions.Def_CorrelatedLocalSearch_reflMatrix

set_option autoImplicit false

open Classical

namespace CorrelatedLocalSearch

/-- The reflected comparison matrix (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22): `R^{(m)}` maps
nonnegative increasing vectors on `{1, …, m − 1}` to nonnegative increasing vectors; and, for a
process satisfying the hypotheses of Lemma C.1 with initial potential `h < m`, the sum of
`k^{−s∗T}` over the surviving words `w` of length `T` all of whose prefixes have potential `< m`
is at most `F_T(h) = ((R^{(m)})^T 𝟙)(h)`.

**Formalization Note** Vectors on `{1, …, L}`, `L = m − 1`, are functions on `Fin (m − 1)`
(index `i` = potential `i + 1`), with the order of `Fin`; "increasing" is nondecreasing. `F_T` is
`reflF`. A word of length `T` is `List.ofFn v`, `v : Fin T → Fin k`. -/
theorem reflected_matrix_bound (k r : ℕ) (hk : k < 2 * r) (hr : r < k) (m : ℕ) (hm : 2 ≤ m) :
    (∀ f : Fin (m - 1) → ℝ, (∀ i, 0 ≤ f i) → Monotone f →
        (∀ i, 0 ≤ (reflMatrix k r m).mulVec f i) ∧ Monotone ((reflMatrix k r m).mulVec f)) ∧
      ∀ (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ),
        IsPotentialProcess k r live pot h → h < m → ∀ T : ℕ,
          ∑ v : Fin T → Fin k,
              (if Surv live (List.ofFn v) ∧ (∀ u : List (Fin k), u <+: List.ofFn v → pot u < m)
                then (k : ℝ) ^ (-(sStar k r * T)) else 0) ≤ reflF k r m T h := by sorry

end CorrelatedLocalSearch
