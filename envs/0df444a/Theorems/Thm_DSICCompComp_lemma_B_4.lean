-- Prove2me | Theorems.Thm_DSICCompComp_lemma_B_4
-- name    : DSICCompComp.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:32:14.814271+00:00
-- url     : https://prove2.me/theorems/60f64792-b2be-49c3-ae40-306b1f885323
-- title:
--   Lemma B.4 — tail of the bundle price: $\mathbb P[p_{i,\{j,k\}}(v_{-i}) - 2a \ge x] \le \Phi(x)$
-- statement:
--   Let $D$ be the distribution of Section 3.2 with $a \ge 1$, $b \in (0,1)$, let $\varepsilon, T > 0$, $0 < t < a$ and $\ell \le m$. Let $i$ be a non-reserve bidder and $j \ne k$ items in $[\ell]$. For every $x > T$, with $v \sim (D^m)^n$,
--   $$
--   \mathbb P\bigl[p_{i,\{j,k\}}(v_{-i}) - 2a \ge x\bigr] \;\le\; \Phi(x) \;\le\; 16\Bigl(nb\Bigl(\frac1t + \frac{t(1+\ell b)}{a-t}\Bigr) + \frac{n\ell b^2 + rb\varepsilon}{x - T}\Bigr),
--   $$
--   where
--   $$
--   \Phi(x) = 2b(n-r)\Bigl(\frac{1}{t+1} + \frac{t(1+b(\ell-1))}{a-t}\Bigr) + \frac{16b^2(n-r-1)(\ell-1)}{T+x+4} + \frac{4rb\varepsilon}{x-T+2\varepsilon}
--   $$
--   is the bound printed in the proof. In particular
--   $\mathbb P[p_{i,\{j,k\}}(v_{-i}) - 2a \ge x] \le O\bigl(nb(1/t + t(1+\ell b)/(a-t)) + (n\ell b^2 + rb\varepsilon)/(x-T)\bigr)$.
--
--   The bundle price of a non-reserve bidder is rarely much above $2a + T$; Lemmas B.5 and B.6 use this to show that bundles are bought often.
--
--   Differences from the source:
--   - reading: ≤ O(nb(1/t + t(1+ℓb)/(a−t)) + (nℓb²+rbε)/(x−T)) → ≤ Φ(x) (the bound printed in the proof) ∧ Φ(x) ≤ 16·(nb(1/t + t(1+ℓb)/(a−t)) + (nℓb²+rbε)/(x−T)); reason: the explicit form of the O with constant 16; stronger than ∃ C
--   - reading: no condition relating t and a → 0 < t < a; reason: a − t is a value threshold and a denominator in the proof
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma B.4, p.28 (pdf p.29); explicit bound at the end of its proof, p.30 (pdf p.31)

import Mathlib
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_menuPrice
import Definitions.Def_DSICCompComp_phiB4

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma B.4 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma B.4, p.28 (pdf p.29); explicit bound at the end of its proof, p.30
(pdf p.31)): let `i` be a non-reserve bidder and `j ≠ k ∈ [ℓ]`. For `x > T`, with `v ∼ (D^m)^n`,
`P[p_{i,{j,k}}(v_{−i}) − 2a ≥ x] ≤ Φ(x) ≤ 16·(nb·(1/t + t(1 + ℓb)/(a − t)) + (nℓb² + rbε)/(x − T))`,
where `Φ = phiB4` is the bound printed in the proof; this gives the printed
`O(nb·(1/t + t(1 + ℓb)/(a − t)) + (nℓb² + rbε)/(x − T))` with constant `16`.

**Formalization Note** `t < a` is assumed (`a − t` is a value threshold and a denominator in the
proof). Non-reserve bidder: `r ≤ i` (0-based). -/
theorem lemma_B_4 (n m ℓ r : ℕ) (hℓm : ℓ ≤ m) (a b ε t T : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b)
    (hb1 : b < 1) (hε : 0 < ε) (hT : 0 < T) (ht0 : 0 < t) (hta : t < a) (i : Fin n)
    (hi : r ≤ i.val) (j k : Fin m) (hjk : j ≠ k) (hj : j.val < ℓ) (hk : k.val < ℓ) (x : ℝ)
    (hx : T < x) :
    (profileLaw n fun _ : Fin m => hardDist a b)
        {v | x ≤ menuPrice ℓ r a ε t T i {j, k} v - 2 * a} ≤
      ENNReal.ofReal (phiB4 n ℓ r a b ε t T x) ∧
    phiB4 n ℓ r a b ε t T x ≤
      16 * (n * b * (1 / t + t * (1 + ℓ * b) / (a - t)) + (n * ℓ * b ^ 2 + r * b * ε) / (x - T)) := by sorry

end DSICCompComp
