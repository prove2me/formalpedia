-- Prove2me | Theorems.Thm_DSICCompComp_lemma_B_5
-- name    : DSICCompComp.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:32:31.273467+00:00
-- url     : https://prove2.me/theorems/7d557eb4-8cbb-485a-8f5d-a3c92e846ebe
-- title:
--   Lemma B.5 — excess bundle revenue on the event $E_{ijk}$ (corrected: $t \le a(1-b)$)
-- statement:
--   Let $D$ be the distribution of Section 3.2 with $a \ge 1$, $b \in (0,1)$, let $\varepsilon > 0$, $3 \le T < s \le t \le a(1-b)$ and $\ell \le m$. Let $i$ be a non-reserve bidder and $j \ne k$ items in $[\ell]$, and let $E_{ijk}$ be the event that $v_{ij}, v_{ik} \ge a$, $v_{ih} < a - t$ for all $h \in [\ell]\setminus\{j,k\}$, and $v_{ij} + v_{ik} > p_{i,\{j,k\}}(v_{-i})$. With $v \sim (D^m)^n$,
--   $$
--   \mathbb E_v\Bigl[\bigl(p_{i,\{j,k\}}(v_{-i}) - 2(a-1)\bigr)\cdot\mathbb 1\bigl(E_{ijk},\ p_{i,\{j,k\}}(v_{-i}) - 2a < t\bigr)\Bigr] \;\ge\; b^2\Bigl(1 - \frac{ab}{a-t}\Bigr)^{\ell-2}\cdot\Bigl(2\bigl(1 - \Phi(t)\bigr) + \frac{2\log(s+1)}{s+2}\bigl(1 - \Phi(s)\bigr)\Bigr),
--   $$
--   where $\Phi$ is the bound of Lemma B.4 (the paper writes $1 - O(\cdot)$ for $1 - \Phi(\cdot)$).
--
--   Differences from the source:
--   - reading: 1 − O(nb(1/t + t(1+ℓb)/(a−t)) + (nℓb²+rbε)/(x−T)) at x = t and x = s → 1 − Φ(t) and 1 − Φ(s), with Φ the bound of Lemma B.4; reason: the proof applies Lemma B.4's explicit bound; an ∃ C reading of 1 − O(·) is vacuous (a large C makes the right side negative)
--   - reading: T unrestricted in the statement → 3 ≤ T; reason: the proof states it: "T ≥ 3 suffices" for log(x + 1)/(x + 2) to be decreasing after T (p.31)
--   - correction: all T < s ≤ t (and t < a, where Φ is defined) → t ≤ a(1 − b); reason: the printed lemma is false: n = 1, r = 0, ℓ = m = 4, a = 100, b = 0.99, ε = 1, T = 3, s = t = 5: Φ(5) = 1.98·(1/6 + 5·3.97/95) ≈ 0.744, so the right side is about 0.9801·(4/95)²·0.644 ≈ 0.0011 > 0, while E_ijk needs v_ih < a − t = 95 < ab = 99 for two items h, an event of probability 0, so the left side is 0; the proof's step P[v_ih < a − t] = 1 − ab/(a − t) needs a − t ≥ ab
--   - encoding: E[X·𝟙(E)] for a nonnegative X → ∫⁻ over the event E of ENNReal.ofReal X, compared with ENNReal.ofReal of the right side; reason: X ≥ 0 on E, so both are the same number; a negative right side is the trivial bound 0 in both
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma B.5, p.30 (pdf p.31)

import Mathlib
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_menuPrice
import Definitions.Def_DSICCompComp_phiB4

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma B.5, corrected (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma B.5, p.30 (pdf p.31)): let `i` be a non-reserve bidder and
`j ≠ k ∈ [ℓ]`, and let `E_{ijk}` be the event `v_{ij}, v_{ik} ≥ a`, `v_{ih} < a − t` for all
`h ∈ [ℓ]∖{j, k}`, and `v_{ij} + v_{ik} > p_{i,{j,k}}(v_{−i})`. For all `T < s ≤ t`, with `v ∼ (D^m)^n`,
`E_v[(p_{i,{j,k}}(v_{−i}) − 2(a − 1))·𝟙(E_{ijk}, p_{i,{j,k}}(v_{−i}) − 2a < t)] ≥
b²(1 − ab/(a − t))^{ℓ−2}·(2(1 − Φ(t)) + (2 log(s + 1)/(s + 2))·(1 − Φ(s)))`,
with `Φ = phiB4` the bound of Lemma B.4 in place of the printed `O(·)`.

**Formalization Note** `T ≥ 3` is the condition stated in the proof ("T ≥ 3 suffices", p.31).
Correction: `t ≤ a(1 − b)` is added (the printed lemma is false for `n = 1, r = 0, ℓ = m = 4,
a = 100, b = 0.99, ε = 1, T = 3, s = t = 5`). The expectation of the nonnegative integrand is `∫⁻`
over the event of `ENNReal.ofReal`. -/
theorem lemma_B_5 (n m ℓ r : ℕ) (hℓm : ℓ ≤ m) (a b ε t T s : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b)
    (hb1 : b < 1) (hε : 0 < ε) (hT : 3 ≤ T) (hTs : T < s) (hst : s ≤ t)
    (hta : t ≤ a * (1 - b)) (i : Fin n) (hi : r ≤ i.val) (j k : Fin m) (hjk : j ≠ k)
    (hj : j.val < ℓ) (hk : k.val < ℓ) :
    ENNReal.ofReal (b ^ 2 * (1 - a * b / (a - t)) ^ (ℓ - 2) *
        (2 * (1 - phiB4 n ℓ r a b ε t T t) +
          2 * Real.log (s + 1) / (s + 2) * (1 - phiB4 n ℓ r a b ε t T s))) ≤
      ∫⁻ v in {v : Fin n → Fin m → ℝ≥0 | (a ≤ (v i j : ℝ) ∧ a ≤ (v i k : ℝ) ∧
            (∀ h : Fin m, h.val < ℓ → h ≠ j → h ≠ k → (v i h : ℝ) < a - t) ∧
            menuPrice ℓ r a ε t T i {j, k} v < (v i j : ℝ) + v i k) ∧
          menuPrice ℓ r a ε t T i {j, k} v - 2 * a < t},
        ENNReal.ofReal (menuPrice ℓ r a ε t T i {j, k} v - 2 * (a - 1))
        ∂(profileLaw n fun _ : Fin m => hardDist a b) := by sorry

end DSICCompComp
