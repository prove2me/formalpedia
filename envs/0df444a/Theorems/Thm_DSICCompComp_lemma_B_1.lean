-- Prove2me | Theorems.Thm_DSICCompComp_lemma_B_1
-- name    : DSICCompComp.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:32:18.706767+00:00
-- url     : https://prove2.me/theorems/d14a0899-de6a-46da-ad89-3554d6658102
-- title:
--   Lemma B.1 — excess singleton revenue from a non-reserve bidder (corrected: $t \le a(1-b)$)
-- statement:
--   Let $D$ be the distribution of Section 3.2 with $a \ge 1$, $b \in (0,1)$, let $\varepsilon, T > 0$ and $0 < t \le a(1-b)$, and let $\ell \le m$. Let $i$ be a non-reserve bidder and $j \in [\ell]$. Given the other bidders' values $v_{-i}$, with $v_i \sim D^m$,
--   $$
--   \mathbb E_{v_i}\bigl[(p_i(v) - (a-1))\cdot\mathbb 1(S_i(v) = \{j\})\bigr] \;\ge\; b\cdot\Bigl(1 - \frac{ab}{a-t}\Bigr)^{\ell-1},
--   $$
--   where $S_i(v)$ and $p_i(v) = p_{i,S_i(v)}(v_{-i})$ are the affine maximizer's allocation and Clarke pivot payment.
--
--   This is the revenue a non-reserve bidder contributes, beyond $a-1$ per item, when she buys exactly one item.
--
--   Differences from the source:
--   - correction: all t > 0 → 0 < t ≤ a(1 − b); reason: the printed lemma is false: a = 10, b = 1/2, t = 8, ℓ = 3 (any n > r, ε, T > 0): the right side is (1/2)(1 − 5/2)² = 1.125, while on {S_i = {j}} the price P = p_{i,{j}} ≥ a + t and v_ij ≥ P, so the left side is at most (P − (a − 1))·b/(P − a + 1) = b = 1/2; the proof's step P[v_ik ≤ a − t] = 1 − ab/(a − t) needs a − t ≥ ab, and §B.4's parameters (t = √a, b < 1/2) satisfy it
--   - encoding: given v_{−i}, E over v_i → for every profile v, ∫⁻ over x ∼ D^m with row i of v replaced by x; reason: same conditional expectation
--   - encoding: E[X·𝟙(E)] for a nonnegative X → ∫⁻ over the event E of ENNReal.ofReal X, compared with ENNReal.ofReal of the right side; reason: X ≥ 0 on E, so both are the same number; a negative right side is the trivial bound 0 in both
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma B.1, p.25 (pdf p.26)

import Mathlib
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_amAlloc
import Definitions.Def_DSICCompComp_menuPrice

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma B.1, corrected (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma B.1, p.25 (pdf p.26)): let `i` be a non-reserve bidder and
`j ∈ [ℓ]`. Given `v_{−i}`, with `v_i ∼ D^m` (`D` of §3.2),
`E_{v_i}[(p_i(v) − (a − 1))·𝟙(S_i(v) = {j})] ≥ b·(1 − ab/(a − t))^{ℓ−1}`,
where `S_i(v)` and `p_i(v) = p_{i,S_i(v)}(v_{−i})` are the affine maximizer's allocation and
payment.

**Formalization Note** Correction: `t ≤ a(1 − b)` is added (the printed lemma has all `t > 0`
and is false for `a = 10, b = 1/2, t = 8, ℓ = 3`). The expectation of the nonnegative integrand is
`∫⁻` over the event of `ENNReal.ofReal`; `v_i` replaces row `i` of the arbitrary profile `v`. -/
theorem lemma_B_1 (n m ℓ r : ℕ) (hℓm : ℓ ≤ m) (a b ε t T : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b)
    (hb1 : b < 1) (hε : 0 < ε) (hT : 0 < T) (ht0 : 0 < t) (hta : t ≤ a * (1 - b))
    (i : Fin n) (hi : r ≤ i.val) (j : Fin m) (hj : j.val < ℓ) (v : Fin n → Fin m → ℝ≥0) :
    ENNReal.ofReal (b * (1 - a * b / (a - t)) ^ (ℓ - 1)) ≤
      ∫⁻ x in {x : Fin m → ℝ≥0 | amAlloc ℓ r a ε t T (Function.update v i x) i = {j}},
        ENNReal.ofReal
          (menuPrice ℓ r a ε t T i (amAlloc ℓ r a ε t T (Function.update v i x) i)
            (Function.update v i x) - (a - 1))
        ∂(Measure.pi fun _ : Fin m => (hardDist a b : Measure ℝ≥0)) := by sorry

end DSICCompComp
