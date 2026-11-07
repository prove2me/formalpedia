-- Prove2me | Theorems.Thm_AC02Frege_lemma_C_1_cumulative_counts
-- name    : AC02Frege.lemma_C_1_cumulative_counts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:47.606132+00:00
-- url     : https://prove2.me/theorems/aeb3c46d-afbb-4fd9-853d-b9c0de5e8974
-- title:
--   Lemma C.1 — cumulative monomial counts near half the variables
-- statement:
--   Let $n\ge2$, $a\ge1$, $N=n\ell$ and $\sqrt\ell\ge128(a+2)$. For $K=\lfloor N/2-an\sqrt\ell\rfloor$ and $1\le r\le n$,
--   $$
--   \frac12\,\frac{M_N(K-r)}{M_N(K)}\ \ge\ \frac12\exp\Bigl(-64(a+2)\frac{r}{\sqrt\ell}\Bigr).
--   $$
--
--   Near half the variables the binomial coefficients are flat, so each factor of an approximator removes a fraction $\eta$ of the error conditions that is only $e^{-O(r/\sqrt\ell)}$ small.
--
--   Differences from the source:
--   - encoding: K = ⌊N/2 − an√ℓ⌋, M_N(K − r) → the natural-number floor and natural subtraction; reason: under the hypotheses N/2 − an√ℓ > 0 and K ≥ r, so both agree with the integer values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma C.1, p.46; (35), p.27

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_rankCounts

namespace AC02Frege

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma C.1, p.46 (cumulative monomial counts near half the variables; (35), p.27): let
`n ≥ 2`, `a ≥ 1`, `N = nℓ`, and `√ℓ ≥ 128(a + 2)`. For `K = ⌊N/2 − an√ℓ⌋` and `1 ≤ r ≤ n`,
`½ M_N(K − r)/M_N(K) ≥ ½ exp(−64(a + 2) r/√ℓ)`.

**Formalization Note** The left side is `etaFrac N K r`; `ℓ` need not be odd. -/
theorem lemma_C_1_cumulative_counts (n ℓ r : ℕ) (a : ℝ) (hn : 2 ≤ n) (ha : 1 ≤ a)
    (hℓ : 128 * (a + 2) ≤ Real.sqrt ℓ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    (1 / 2 : ℝ) * Real.exp (-(64 * (a + 2) * r / Real.sqrt ℓ)) ≤
      etaFrac (n * ℓ) ⌊((n * ℓ : ℕ) : ℝ) / 2 - a * n * Real.sqrt ℓ⌋₊ r := by sorry

end AC02Frege
