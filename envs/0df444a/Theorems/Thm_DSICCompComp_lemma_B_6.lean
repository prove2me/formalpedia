-- Prove2me | Theorems.Thm_DSICCompComp_lemma_B_6
-- name    : DSICCompComp.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:33:20.85764+00:00
-- url     : https://prove2.me/theorems/8959626a-d9c7-4843-83be-f17b511dbd05
-- title:
--   Lemma B.6 — excess bundle revenue from a non-reserve bidder (corrected: $t \le a(1-b)$)
-- statement:
--   Under the hypotheses of Lemma B.5 ($a \ge 1$, $b \in (0,1)$, $\varepsilon > 0$, $3 \le T < s \le t \le a(1-b)$, $\ell \le m$), let $i$ be a non-reserve bidder and $j \ne k$ items in $[\ell]$. With $v \sim (D^m)^n$,
--   $$
--   \mathbb E_v\bigl[(p_i(v) - 2(a-1))\cdot\mathbb 1(S_i(v) = \{j,k\})\bigr] \;\ge\; b^2\Bigl(1 - \frac{ab}{a-t}\Bigr)^{\ell-2}\cdot\Bigl(2\bigl(1 - \Phi(t)\bigr) + \frac{2\log(s+1)}{s+2}\bigl(1 - \Phi(s)\bigr)\Bigr),
--   $$
--   where $S_i(v)$ and $p_i(v)$ are the affine maximizer's allocation and Clarke pivot payment and $\Phi$ is the bound of Lemma B.4.
--
--   Summed over the non-reserve bidders and the pairs $j < k$, this is the bundle term of the revenue bound of §B.4, the term responsible for the $\Omega(\log\lambda)$ gain.
--
--   Differences from the source:
--   - reading: 1 − O(·) at t and s → 1 − Φ(t) and 1 − Φ(s), with Φ the bound of Lemma B.4; reason: the proof applies Lemma B.5; an ∃ C reading is vacuous
--   - reading: T unrestricted in the statement → 3 ≤ T; reason: inherited from Lemma B.5, which the proof applies
--   - correction: all T < s ≤ t (and t < a, where Φ is defined) → t ≤ a(1 − b); reason: the printed lemma is false: n = 2, r = 1, i = 1, ℓ = m = 3, a = 10, b = 1/2, ε = 1, T = 3, s = 4, t = 9.9: the right side is (1/4)(1 − 50)(2(1 − Φ(9.9)) + (2 log 5/6)(1 − Φ(4))) ≈ (1/4)(−49)(−500.7) ≈ 6100, while given v_{−i} the price P = p_{i,{j,k}} ≥ 2a + T and S_i = {j,k} forces v_ij + v_ik ≥ P, so the left side is at most (P − 2a + 2)·2b/(P/2 − a + 1) = 4b = 2; it inherits the gap of Lemma B.5
--   - encoding: E[X·𝟙(E)] for a nonnegative X → ∫⁻ over the event E of ENNReal.ofReal X, compared with ENNReal.ofReal of the right side; reason: X ≥ 0 on E, so both are the same number; a negative right side is the trivial bound 0 in both
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma B.6, p.31 (pdf p.32)

import Mathlib
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_amAlloc
import Definitions.Def_DSICCompComp_menuPrice
import Definitions.Def_DSICCompComp_phiB4

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma B.6, corrected (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma B.6, p.31 (pdf p.32)): let `i` be a non-reserve bidder and
`j ≠ k ∈ [ℓ]`. For all `T < s ≤ t`, with `v ∼ (D^m)^n`,
`E_v[(p_i(v) − 2(a − 1))·𝟙(S_i(v) = {j, k})] ≥
b²(1 − ab/(a − t))^{ℓ−2}·(2(1 − Φ(t)) + (2 log(s + 1)/(s + 2))·(1 − Φ(s)))`,
where `S_i(v)` and `p_i(v) = p_{i,S_i(v)}(v_{−i})` are the affine maximizer's allocation and
payment, and `Φ = phiB4` is the bound of Lemma B.4 in place of the printed `O(·)`.

**Formalization Note** `T ≥ 3` (stated in the proof of Lemma B.5, which this proof applies).
Correction: `t ≤ a(1 − b)` is added (for `ℓ = 3` the printed right side tends to `+∞` as
`t ↑ a` while the left side stays below `4b`). The expectation of the nonnegative integrand is
`∫⁻` over the event of `ENNReal.ofReal`. -/
theorem lemma_B_6 (n m ℓ r : ℕ) (hℓm : ℓ ≤ m) (a b ε t T s : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b)
    (hb1 : b < 1) (hε : 0 < ε) (hT : 3 ≤ T) (hTs : T < s) (hst : s ≤ t)
    (hta : t ≤ a * (1 - b)) (i : Fin n) (hi : r ≤ i.val) (j k : Fin m) (hjk : j ≠ k)
    (hj : j.val < ℓ) (hk : k.val < ℓ) :
    ENNReal.ofReal (b ^ 2 * (1 - a * b / (a - t)) ^ (ℓ - 2) *
        (2 * (1 - phiB4 n ℓ r a b ε t T t) +
          2 * Real.log (s + 1) / (s + 2) * (1 - phiB4 n ℓ r a b ε t T s))) ≤
      ∫⁻ v in {v : Fin n → Fin m → ℝ≥0 | amAlloc ℓ r a ε t T v i = {j, k}},
        ENNReal.ofReal (menuPrice ℓ r a ε t T i (amAlloc ℓ r a ε t T v i) v - 2 * (a - 1))
        ∂(profileLaw n fun _ : Fin m => hardDist a b) := by sorry

end DSICCompComp
