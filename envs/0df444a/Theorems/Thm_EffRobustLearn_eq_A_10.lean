-- Prove2me | Theorems.Thm_EffRobustLearn_eq_A_10
-- name    : EffRobustLearn.eq_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:30.522341+00:00
-- url     : https://prove2.me/theorems/c0095612-9311-48e2-b1ec-753de80b16c3
-- title:
--   Eq. (A.10) — pointwise approximation of the sign by $\mathrm{maj}_k$
-- statement:
--   For every integer $k\ge1$ and every $\mu\in[-1,1]$,
--   $$0\le(\mathrm{sign}(\mu)-\mathrm{maj}_k(\mu))\mu\le\frac2{\sqrt k}.$$
--
--   This bounds the price of replacing the sign of an iterate by the smooth majority vote, and it is what forces $k=\lceil64/\varepsilon^2\rceil$ in Algorithm 1.
--
--   Differences from the source:
--   - reading: $\mathrm{sign}(0)$ unspecified → $\mathrm{sign}(0)=+1$; reason: $\mathrm{Maj}_k(C)\subseteq\{\pm1\}^X$ needs a $\pm1$ value; at $\mu=0$ the expression vanishes under any choice
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (A.10), p.32 (PDF p.33), cited from [Bla26, Claim 8.3]

import Mathlib
import Definitions.Def_EffRobustLearn_signPM
import Definitions.Def_EffRobustLearn_majK

namespace EffRobustLearn

/-- Eq. (A.10), p.32 (arXiv:2609.17655, held version, sha256 312a0857…), cited there from [Bla26, Claim 8.3]: for every `μ ∈ [-1, 1]`,
`0 ≤ (sign(μ) - maj_k(μ)) μ ≤ 2/√k`.

**Formalization Note.** `k ≥ 1`, the range of (2.2), and `sign 0 = +1` (`signPM`). -/
theorem eq_A_10 (k : ℕ) (hk : 1 ≤ k) (μ : ℝ) (h1 : -1 ≤ μ) (h2 : μ ≤ 1) :
    0 ≤ (signPM μ - majK k μ) * μ ∧ (signPM μ - majK k μ) * μ ≤ 2 / Real.sqrt k := by sorry

end EffRobustLearn
