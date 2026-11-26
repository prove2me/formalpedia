-- Prove2me | Theorems.Thm_Erdos287_wide_endpoint_ratio_above_main3
-- name    : Erdos287.wide_endpoint_ratio_above_main3
-- status  : Open
-- author  : @immiq
-- created : 2026-11-26T11:08:18.211409+00:00
-- url     : https://prove2.me/theorems/2876a80f-eb32-4094-ba8f-f635f5968064
-- title:
--   Wide endpoint-ratio branch above the Main3 finite certificate
-- statement:
--   Exclude any no-gap counterexample with $250M>739m$ and $M>381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435$. Here $m$ and $M$ are the least and greatest selected denominators. The continuous Main3 Lean certificate excludes every smaller maximum.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.wide_endpoint_ratio_above_main3 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hlarge : 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435 < f (k - 1))
    (hwide : 739 * f 0 < 250 * f (k - 1)) : False := by sorry
