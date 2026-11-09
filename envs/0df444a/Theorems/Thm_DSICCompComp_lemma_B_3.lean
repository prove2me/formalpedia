-- Prove2me | Theorems.Thm_DSICCompComp_lemma_B_3
-- name    : DSICCompComp.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:32:28.158113+00:00
-- url     : https://prove2.me/theorems/ce5d8840-a8c5-49f8-9861-e481cb5a5dcd
-- title:
--   Lemma B.3 — $\mathbb E_v[p_i(v) - a|S_i(v)|]$ for a reserve bidder
-- statement:
--   Under the hypotheses of Lemma B.2 ($a \ge 1$, $b \in (0,1)$, $\varepsilon, t, T > 0$, $\ell \le m$, $r \le n$, $rb \ge \sqrt e$), let $i$ be a reserve bidder. With $v \sim (D^m)^n$,
--   $$
--   \mathbb E_v\bigl[p_i(v) - a\cdot|S_i(v)|\bigr] \;\ge\; \ell b\cdot\Bigl(1 - \frac{1-(1-b)^r}{rb} - (\ell-1)\cdot\frac{\log(rb) + 1/2}{r}\Bigr),
--   $$
--   where $S_i(v)$ and $p_i(v)$ are the affine maximizer's allocation and Clarke pivot payment.
--
--   Summed over the $r$ reserve bidders, this is the reserve-bidder term of the revenue bound of §B.4.
--
--   Differences from the source:
--   - reading: no condition on r, b in the statement → rb ≥ √e; reason: the proof applies Lemma B.2, whose proof needs it
--   - encoding: E_v[p_i(v) − a|S_i(v)|] → ∫⁻ of ENNReal.ofReal (p_i(v) − a|S_i(v)|), compared with ENNReal.ofReal of the right side; reason: p_i − a|S_i| = (OPT_{−i,−∅} − OPT_{−i,−S_i})/ε ≥ 0
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma B.3, p.27 (pdf p.28)

import Mathlib
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_amAlloc
import Definitions.Def_DSICCompComp_menuPrice

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma B.3 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma B.3, p.27 (pdf p.28)): for a reserve bidder `i`, with `v ∼ (D^m)^n`
(`D` of §3.2),
`E_v[p_i(v) − a·|S_i(v)|] ≥ ℓb·(1 − (1 − (1 − b)^r)/(rb) − (ℓ − 1)·(log(rb) + 1/2)/r)`,
where `S_i(v)` and `p_i(v) = p_{i,S_i(v)}(v_{−i})` are the affine maximizer's allocation and
payment.

**Formalization Note** `rb ≥ √e` is the condition of Lemma B.2, which the proof applies.
Reserve bidder: `i < r` (0-based). The integrand `p_i − a|S_i| = (OPT_{−i,−∅} − OPT_{−i,−S_i})/ε`
is nonnegative; its expectation is `∫⁻` of `ENNReal.ofReal`. -/
theorem lemma_B_3 (n m ℓ r : ℕ) (hℓm : ℓ ≤ m) (hrn : r ≤ n) (a b ε t T : ℝ) (ha : 1 ≤ a)
    (hb0 : 0 < b) (hb1 : b < 1) (hε : 0 < ε) (ht : 0 < t) (hT : 0 < T)
    (hrb : Real.sqrt (Real.exp 1) ≤ r * b) (i : Fin n) (hi : i.val < r) :
    ENNReal.ofReal (ℓ * b * (1 - (1 - (1 - b) ^ r) / (r * b) - ((ℓ : ℝ) - 1) * (Real.log (r * b) + 1 / 2) / r)) ≤
      ∫⁻ v, ENNReal.ofReal
          (menuPrice ℓ r a ε t T i (amAlloc ℓ r a ε t T v i) v -
            a * (amAlloc ℓ r a ε t T v i).card)
        ∂(profileLaw n fun _ : Fin m => hardDist a b) := by sorry

end DSICCompComp
