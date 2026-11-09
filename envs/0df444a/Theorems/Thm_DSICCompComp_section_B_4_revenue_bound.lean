-- Prove2me | Theorems.Thm_DSICCompComp_section_B_4_revenue_bound
-- name    : DSICCompComp.section_B_4_revenue_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:33:29.666103+00:00
-- url     : https://prove2.me/theorems/fabe4d87-affa-4b16-8dd7-87d6a5726542
-- title:
--   §B.4 — revenue lower bound for the mechanism $M$ (corrected: $t \le a(1-b)$)
-- statement:
--   Let $D$ be the distribution of Section 3.2 and $M$ the mechanism of Section 3.3, with $1 \le \ell \le m$, $r \le n$, $a \ge 1$, $b \in (0,1)$, $\varepsilon > 0$, $rb \ge \sqrt e$ and $3 \le T < s \le t \le a(1-b)$. Then the expected revenue of $M$ with $n$ bidders whose values are drawn from $D^m$ satisfies
--   $$
--   \begin{aligned}
--   \mathrm{Rev}^M_n(D^m) \;\ge\;& (m-\ell)(a-1)\bigl(1-(1-b)^n\bigr) + (m-\ell)nb + \ell(a-1)\bigl(1-(1-b)^r\bigr)\\
--   &+ r\ell b\Bigl(1 - \frac{1-(1-b)^r}{rb} - (\ell-1)\frac{\log(rb)+1/2}{r}\Bigr) + \ell b(n-r)\Bigl(1-\frac{ab}{a-t}\Bigr)^{\ell-1}\\
--   &+ \binom{\ell}{2} b^2(n-r)\Bigl(1-\frac{ab}{a-t}\Bigr)^{\ell-2}\Bigl(2\bigl(1-\Phi(t)\bigr) + \frac{2\log(s+1)}{s+2}\bigl(1-\Phi(s)\bigr)\Bigr),
--   \end{aligned}
--   $$
--   where $\Phi$ is the bound of Lemma B.4 (the paper writes $1 - O(\cdot)$).
--
--   The first two terms are the revenue from selling the last $m - \ell$ items separately; the rest collects Lemmas B.1, B.3 and B.6 for the affine maximizer.
--
--   Differences from the source:
--   - reading: 1 − O(·) at t and s → 1 − Φ(t) and 1 − Φ(s), with Φ the bound of Lemma B.4; reason: the bound is assembled from Lemma B.6; an ∃ C reading is vacuous
--   - reading: parameters as in Lemmas B.1–B.6, not restated in §B.4 → 1 ≤ ℓ ≤ m, r ≤ n, a ≥ 1, b ∈ (0,1), ε > 0, rb ≥ √e, 3 ≤ T < s ≤ t; reason: the hypotheses of the lemmas the bound combines (ℓ ∈ [m] from §3.3, rb ≥ √e from Lemma B.2, T ≥ 3 from Lemma B.5)
--   - correction: the parameters of Lemmas B.1 and B.6 as printed (any t > 0) → t ≤ a(1 − b); reason: without it the bound is false: n = 5, r = 4 (rb = 2 ≥ √e), m = ℓ = 3, a = 10, b = 1/2, ε = 1, T = 3, s = 4 and t ↑ 10: the singleton term (3/2)(1 − 5/(10 − t))² and the bundle term (3/4)(1 − 5/(10 − t))·(2(1 − Φ(t)) + (2 log 5/6)(1 − Φ(4))) both tend to +∞, while Rev^M_5(D³) ≤ Rev^𝒟_5(D³), which is finite and does not depend on t (each bidder faces a menu, so E[p_i] is at most the optimal one-buyer revenue for three independent items from D, finite by Hart–Nisan's bound by a multiple of SRev; alternatively Rev^𝒟 ≤ Rev^ℬ ≤ SRev_{n+O(√nm)} by [BW19])
--   - encoding: Rev^M_n(D^m) ≥ a real number → the real right side, cast to EReal, ≤ the published expRevenueN of M; reason: the published revenue is an extended real; same comparison
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §B.4, p.33 (pdf p.34)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Definitions.Def_DSICCompComp_profileLaw
import Definitions.Def_DSICCompComp_hardDist
import Definitions.Def_DSICCompComp_mechM
import Definitions.Def_DSICCompComp_phiB4

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- §B.4, the revenue lower bound for `M` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §B.4, p.33 (pdf p.34)): with `v ∼ (D^m)^n`
(`D` of §3.2) and `M` the mechanism of §3.3,
`Rev^M_n(D^m) ≥ (m − ℓ)(a − 1)(1 − (1 − b)^n) + (m − ℓ)nb + ℓ(a − 1)(1 − (1 − b)^r)
 + rℓb·(1 − (1 − (1 − b)^r)/(rb) − (ℓ − 1)·(log(rb) + 1/2)/r) + ℓb(n − r)(1 − ab/(a − t))^{ℓ−1}
 + C(ℓ, 2)·b²(n − r)(1 − ab/(a − t))^{ℓ−2}·(2(1 − Φ(t)) + (2 log(s + 1)/(s + 2))·(1 − Φ(s)))`,
with `Φ = phiB4` the bound of Lemma B.4 in place of the printed `O(·)`.

**Formalization Note** The hypotheses are those of the lemmas the bound combines: `ℓ ∈ [m]`,
`r ≤ n`, `a ≥ 1`, `b ∈ (0, 1)`, `ε > 0`, `rb ≥ √e` (Lemma B.2), `3 ≤ T < s ≤ t` (Lemma B.5) and the
correction `t ≤ a(1 − b)` (Lemmas B.1, B.5, B.6; without it the bound fails, e.g. for `n = 5,
r = 4, m = ℓ = 3, a = 10, b = 1/2` as `t ↑ a`). The revenue `Rev^M_n` is the published
`expRevenueN` in `EReal`. -/
theorem section_B_4_revenue_bound (n m ℓ r : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ m) (hrn : r ≤ n)
    (a b ε t T s : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b < 1) (hε : 0 < ε) (hT : 3 ≤ T)
    (hTs : T < s) (hst : s ≤ t) (hta : t ≤ a * (1 - b))
    (hrb : Real.sqrt (Real.exp 1) ≤ r * b) :
    ((((m : ℝ) - ℓ) * (a - 1) * (1 - (1 - b) ^ n) + ((m : ℝ) - ℓ) * n * b +
        ℓ * (a - 1) * (1 - (1 - b) ^ r) +
        r * ℓ * b * (1 - (1 - (1 - b) ^ r) / (r * b) - ((ℓ : ℝ) - 1) * (Real.log (r * b) + 1 / 2) / r) +
        ℓ * b * ((n : ℝ) - r) * (1 - a * b / (a - t)) ^ (ℓ - 1) +
        (ℓ.choose 2 : ℝ) * b ^ 2 * ((n : ℝ) - r) * (1 - a * b / (a - t)) ^ (ℓ - 2) *
          (2 * (1 - phiB4 n ℓ r a b ε t T t) +
            2 * Real.log (s + 1) / (s + 2) * (1 - phiB4 n ℓ r a b ε t T s)) : ℝ) : EReal) ≤
      MultiItemRev.MultiBuyer.expRevenueN (profileLaw n fun _ : Fin m => hardDist a b)
        (mechM n m ℓ r a ε t T) := by sorry

end DSICCompComp
