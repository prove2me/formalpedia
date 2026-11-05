-- Prove2me | Theorems.Thm_BlindNRMLS_lemma_EC_1
-- name    : BlindNRMLS.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:34.065696+00:00
-- url     : https://prove2.me/theorems/1c1ece6c-d6c5-45bc-aceb-5d4adee24068
-- title:
--   Lemma EC.1 (corrected: the sum starts at $r=2$) — $\sum_{r}(t_r-t_{r-1})/\sqrt{t_{r-1}}\le(8\log T/\sqrt K)\,t_1$
-- statement:
--   Let $(t_l)$ be the grid (5) with parameter $\nu$, for $K\ge2$ and $T\ge1$. Then for every $l\le\nu+1$,
--   $$
--   \sum_{r=2}^{l}\frac{t_r-t_{r-1}}{\sqrt{t_{r-1}}}\le\frac{8\log T}{\sqrt K}\,t_1 .
--   $$
--   This bounds the total confidence radius over the epochs, and it fixes the margin that $\gamma$ needs in Theorem 3.
--
--   Differences from the source:
--   - correction: the sum runs over r ∈ [l] → the sum runs over 2 ≤ r ≤ l; reason: the term r = 1 divides by t₀ = 0, and the proof's bound on it, (EC.13), is not valid there
--   - encoding: ν = ν(s,d) → ν is any natural number; reason: every natural number is ν(s,d) for some s
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Lemma EC.1, p.ec27

import Mathlib
import Definitions.Def_BlindNRMLS_nu

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Lemma EC.1 (corrected): for the grid (5) and any `l ∈ [ν + 1]`,
`∑_{2 ≤ r ≤ l} (t_r - t_{r-1})/√t_{r-1} ≤ (8 log T/√K) t_1`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Lemma EC.1, p.ec27.

**Formalization Note.** The page's sum over `r ∈ [l]` has the term `r = 1`, a division by `t_0 = 0`;
the sum starts at `r = 2`, as the proof's bounds need. `ν` is any natural number, not only a value of
`ν(s,d)`; every `ν` is one. For `T ≥ 1` every `t_r` with `r ≥ 1` is at least `1`, so no division
by `0` is left. -/
theorem lemma_EC_1 (T K ν l : ℕ) (hK : 2 ≤ K) (hT : 1 ≤ T) (hl : l ≤ ν + 1) :
    ∑ r ∈ Finset.Icc 2 l,
        ((tSched T K ν r : ℝ) - (tSched T K ν (r - 1) : ℝ)) / Real.sqrt (tSched T K ν (r - 1) : ℝ) ≤
      8 * Real.log T / Real.sqrt K * (tSched T K ν 1 : ℝ) := by sorry

end BlindNRMLS
