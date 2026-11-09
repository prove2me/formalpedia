-- Prove2me | Theorems.Thm_DSICCompComp_lemma_3_4
-- name    : DSICCompComp.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:32:19.406764+00:00
-- url     : https://prove2.me/theorems/f56eb93a-47dc-4623-aae1-72248c739b90
-- title:
--   Lemma 3.4 — $p_{i,\{j,k\}}(v_{-i}) - p_{i,\{j\}}(v_{-i}) \ge a + T - t$
-- statement:
--   Let $i$ be a non-reserve bidder and let $j \ne k$ be items in $[\ell]$. For all values $v_{-i}$ of the other bidders,
--   $$
--   p_{i,\{j,k\}}(v_{-i}) - p_{i,\{j\}}(v_{-i}) \;\ge\; a + T - t .
--   $$
--   That is, the price of a bundle of two items always exceeds the price of either single item by at least $a + T - t$; this is what makes non-reserve bidders with one low value prefer a singleton.
--
--   Differences from the source:
--   - generalization: the standing parameters a ≥ 1, ε, t, T > 0 → all real a, ε, t, T; reason: the bound only uses OPT_{−i,−{j}} ≥ OPT_{−i,−{j,k}}; specializes to the paper's range
--   - encoding: for all v_{−i} → for every profile v (menuPrice depends only on v_{−i}); reason: same quantity
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma 3.4, p.12 (pdf p.13)

import Mathlib
import Definitions.Def_DSICCompComp_menuPrice

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma 3.4 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma 3.4, p.12 (pdf p.13)): for a non-reserve bidder `i` and items
`j ≠ k ∈ [ℓ]`, for all `v_{−i}`, `p_{i,{j,k}}(v_{−i}) − p_{i,{j}}(v_{−i}) ≥ a + T − t`.

**Formalization Note** Non-reserve bidder: `r ≤ i`; items in `[ℓ]`: `j, k < ℓ` (0-based). Stated
for all real `a, ε, t, T`. -/
theorem lemma_3_4 (n m ℓ r : ℕ) (a ε t T : ℝ) (i : Fin n) (hi : r ≤ i.val) (j k : Fin m)
    (hjk : j ≠ k) (hj : j.val < ℓ) (hk : k.val < ℓ) (v : Fin n → Fin m → ℝ≥0) :
    a + T - t ≤ menuPrice ℓ r a ε t T i {j, k} v - menuPrice ℓ r a ε t T i {j} v := by sorry

end DSICCompComp
