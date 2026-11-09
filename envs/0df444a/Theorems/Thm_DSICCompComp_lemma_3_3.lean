-- Prove2me | Theorems.Thm_DSICCompComp_lemma_3_3
-- name    : DSICCompComp.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:20.999515+00:00
-- url     : https://prove2.me/theorems/bae5ebf8-4604-47ed-92a7-3124a1ff437d
-- title:
--   Lemma 3.3 — $\mathrm{SRev}_{n+c}(D^m) = m(a-1)(1-(1-b)^{n+c}) + (n+c)mb$
-- statement:
--   Let $D$ be the distribution of Section 3.2 with $a \ge 1$ and $b \in (0,1)$. For all $n, c, m \in \mathbb N$, the revenue of selling each of $m$ iid items with value distribution $D$ separately (by Myerson's optimal auction) to $n + c$ bidders is
--   $$
--   \mathrm{SRev}_{n+c}(D^m) = m(a-1)\bigl(1-(1-b)^{n+c}\bigr) + (n+c)mb .
--   $$
--
--   The first term is the revenue from virtual values $a-1$ above the reserve; the second, linear in the number of bidders, comes from the equal-revenue tail. Comparing this with the revenue of the mechanism $M$ (§B.4) gives the lower bound on the number of additional bidders.
--
--   Differences from the source:
--   - encoding: SRev_{n+c}(D^m) as a real number → sRev (n + c) … in ℝ≥0∞ equal to ENNReal.ofReal of the right side; reason: the right side is nonnegative for a ≥ 1, b ∈ (0,1)
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Lemma 3.3, p.11 (pdf p.12); proof in Appendix A, p.24 (pdf p.25)

import Mathlib
import Definitions.Def_DSICCompComp_sRev
import Definitions.Def_DSICCompComp_hardDist

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Lemma 3.3 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Lemma 3.3, p.11 (pdf p.12); proof in Appendix A, p.24 (pdf p.25)):
for the distribution `D` of §3.2 with `a ≥ 1`, `b ∈ (0, 1)`, and every `n, c, m`,
`SRev_{n+c}(D^m) = m(a − 1)(1 − (1 − b)^{n+c}) + (n + c)mb`. -/
theorem lemma_3_3 (n c m : ℕ) (a b : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b < 1) :
    sRev (n + c) (fun _ : Fin m => hardDist a b) =
      ENNReal.ofReal ((m : ℝ) * (a - 1) * (1 - (1 - b) ^ (n + c)) + ((n : ℝ) + c) * m * b) := by sorry

end DSICCompComp
