-- Prove2me | Theorems.Thm_Erdos287_proth_pair_excludes_denominator_band
-- name    : Erdos287.proth_pair_excludes_denominator_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:38:06.901697+00:00
-- url     : https://prove2.me/theorems/af4d3972-9525-4a8a-bbad-b8189fceaaeb
-- title:
--   Proth prime pair excludes a band of maximal denominators
-- statement:
--   Let \(P=r2^{e+1}+1>96\) with \(0<r<2^{e+1}\), and let \(Q=r2^{e+2}+1=2P-1\). Suppose there are Proth witnesses for \(P\) and \(Q\). In a strictly increasing unit-fraction representation of \(1\) on denominators greater than \(1\), if the maximum \(M\) satisfies \(Q+2\le M\) and \(2M+20\le5Q\), then some consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Proth certificate and the factorial prime-pair rung.

import Mathlib

theorem Erdos287.proth_pair_excludes_denominator_band (r e a b k : ℕ) (hr : 0 < r) (hrsmall : r < 2 ^ (e + 1))
    (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    let P := r * 2 ^ (e + 1) + 1
    let Q := r * 2 ^ (e + 2) + 1
    let M := f (k - 1)
    96 < P → (a : ZMod P) ^ (r * 2 ^ e) = -1 →
    (b : ZMod Q) ^ (r * 2 ^ (e + 1)) = -1 →
    Q + 2 ≤ M → 2 * M + 20 ≤ 5 * Q →
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
