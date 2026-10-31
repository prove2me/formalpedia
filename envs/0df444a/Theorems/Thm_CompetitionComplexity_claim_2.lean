-- Prove2me | Theorems.Thm_CompetitionComplexity_claim_2
-- name    : CompetitionComplexity.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:45.24064+00:00
-- url     : https://prove2.me/theorems/f86cdcce-feeb-4a7a-a15b-1d8dfb22b7e0
-- title:
--   Claim 2 — $(n/(n-1))^{1/n}x^{(n-1)/n}\ge x$ for $x\in[0,1]$
-- statement:
--   Let $n>1$ be an integer. For every $x\in[0,1]$,
--   $$
--   \Bigl(\frac{n}{n-1}\Bigr)^{1/n}x^{(n-1)/n}\ge x .
--   $$
--   The inequality is used in the proof of Theorem 1 and, with $x=\rho_{\varepsilon,j}$, to show that the recursion (9) is decreasing in $j$ (§5 and Proposition 3).
--
--   Differences from the source: none.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Claim 2, p.13 (in the proof of Theorem 1; n > 1 from Theorem 1)

import Mathlib

namespace CompetitionComplexity

/-- **Claim 2** (in the proof of Theorem 1).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Claim 2, p.13:
"For every x ∈ [0,1] we have (n/(n−1))^{1/n} x^{(n−1)/n} ≥ x."
Context: `n > 1` is an integer (Theorem 1: "For every positive integer n > 1").

**Formalization Note.** Real powers are `Real.rpow`; at `x = 0` both sides are `0`. -/
theorem claim_2 (n : ℕ) (hn : 1 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ≤ ((n : ℝ) / ((n : ℝ) - 1)) ^ (1 / (n : ℝ)) * x ^ (((n : ℝ) - 1) / (n : ℝ)) := by sorry

end CompetitionComplexity
