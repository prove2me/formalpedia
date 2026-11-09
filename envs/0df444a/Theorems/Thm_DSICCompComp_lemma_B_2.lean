-- Prove2me | Theorems.Thm_DSICCompComp_lemma_B_2
-- name    : DSICCompComp.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:32:04.497203+00:00
-- url     : https://prove2.me/theorems/d162739a-b4e4-4e44-9a3e-5291243c3812
-- title:
--   Lemma B.2 — excess revenue from a reserve bidder on the event $E_{ij}$
-- statement:
--   Let $D$ be the distribution of Section 3.2 with $a \ge 1$, $b \in (0,1)$, let $\varepsilon, t, T > 0$, $\ell \le m$, $r \le n$, and suppose $rb \ge \sqrt e$. Let $i$ be a reserve bidder and $j \in [\ell]$, and let $E_{ij}$ be the event
--   $$
--   v_{ij} - p_{i,\{j\}}(v_{-i}) > \sum_{k\in[\ell]\setminus\{j\}} (v_{ik} - a)_+ .
--   $$
--   With $v \sim (D^m)^n$,
--   $$
--   \mathbb E_v\bigl[(p_{i,\{j\}}(v_{-i}) - a)\cdot\mathbb 1(E_{ij})\bigr] \;\ge\; b\cdot\Bigl(1 - \frac{1-(1-b)^r}{rb} - (\ell-1)\cdot\frac{\log(rb) + 1/2}{r}\Bigr).
--   $$
--
--   On $E_{ij}$ the reserve bidder $i$ buys item $j$; the lemma bounds the revenue in excess of $a$ that this generates.
--
--   Differences from the source:
--   - reading: no condition on r, b in the statement → rb ≥ √e; reason: the proof states it ("Equation 3; if rb ≥ √e", p.27): −y log y + y/2 is increasing for y ≤ e^{−1/2}
--   - encoding: E[X·𝟙(E)] for a nonnegative X → ∫⁻ over the event E of ENNReal.ofReal X, compared with ENNReal.ofReal of the right side; reason: X ≥ 0 on E, so both are the same number; a negative right side is the trivial bound 0 in both
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma B.2, p.25 (pdf p.26)

import Mathlib
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_menuPrice

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma B.2 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma B.2, p.25 (pdf p.26)): let `i` be a reserve bidder and `j ∈ [ℓ]`,
and let `E_{ij}` be the event `v_{ij} − p_{i,{j}}(v_{−i}) > ∑_{k ∈ [ℓ]∖{j}} (v_{ik} − a)₊`.
With `v ∼ (D^m)^n` (`D` of §3.2),
`E_v[(p_{i,{j}}(v_{−i}) − a)·𝟙(E_{ij})] ≥ b·(1 − (1 − (1 − b)^r)/(rb) − (ℓ − 1)·(log(rb) + 1/2)/r)`.

**Formalization Note** `rb ≥ √e` is the condition stated in the proof (Equation 3, p.27).
Reserve bidder: `i < r` (0-based). The expectation of the nonnegative integrand is `∫⁻` over
the event of `ENNReal.ofReal`. -/
theorem lemma_B_2 (n m ℓ r : ℕ) (hℓm : ℓ ≤ m) (hrn : r ≤ n) (a b ε t T : ℝ) (ha : 1 ≤ a)
    (hb0 : 0 < b) (hb1 : b < 1) (hε : 0 < ε) (ht : 0 < t) (hT : 0 < T)
    (hrb : Real.sqrt (Real.exp 1) ≤ r * b) (i : Fin n) (hi : i.val < r) (j : Fin m)
    (hj : j.val < ℓ) :
    ENNReal.ofReal (b * (1 - (1 - (1 - b) ^ r) / (r * b) - ((ℓ : ℝ) - 1) * (Real.log (r * b) + 1 / 2) / r)) ≤
      ∫⁻ v in {v : Fin n → Fin m → ℝ≥0 | menuPrice ℓ r a ε t T i {j} v +
          ∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < ℓ ∧ k ≠ j), max ((v i k : ℝ) - a) 0 <
          (v i j : ℝ)},
        ENNReal.ofReal (menuPrice ℓ r a ε t T i {j} v - a)
        ∂(profileLaw n fun _ : Fin m => hardDist a b) := by sorry

end DSICCompComp
