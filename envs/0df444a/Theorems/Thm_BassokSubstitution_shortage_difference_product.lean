-- Prove2me | Theorems.Thm_BassokSubstitution_shortage_difference_product
-- name    : BassokSubstitution.shortage_difference_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:46:31.89545+00:00
-- url     : https://prove2.me/theorems/c8d8434d-4d4b-45ed-be11-1b17abefd36f
-- title:
--   Lemma 3 — product form for a difference of salvage probabilities
-- statement:
--   Consider the model with Assumptions 1–3, $b \ge 0$, independent nonnegative demands with densities and finite means, and stock levels $y \ge 0$. For products $j < i$,
--   $$\Pr\{\vec S^{j+1}_{i,N} > 0,\ \vec S^j_{i,N} = 0\} - \Pr\{\vec S^{j+1}_{i+1,N} > 0,\ \vec S^j_{i+1,N} = 0\} = \Pr\{S^{j+1}_i > 0,\ \vec S^j_{j,i} = 0\}\,\Pr\{\vec S^{i+1}_{i+1,N} = 0\}.$$
--   Here $\vec S^k_{a,n} = 0$ means $S^k_m = 0$ for all $a \le m \le n$, and $\vec S^k_{a,n} > 0$ is its negation.
--
--   The left side is the difference between the salvage coefficients of product $j$ in $\partial P/\partial y_i$ and in $\partial P/\partial y_{i+1}$ (term (4b)); the lemma rewrites it as a product, which is how the salvage terms are grouped in Lemma 6 and in the proof of Theorem 2.
--
--   **Formalization Note.** The paper leaves $j$ implicit; its use in the proof of Lemma 6 (Appendix B, p. 641) has $1 \le j < i$. For $i = N$ the vectors indexed $i+1, \dots, N$ are empty: $\vec S^{\,\cdot}_{N+1,N} = 0$ holds vacuously, so the second probability on the left is $0$ and the last factor is $1$. The product form needs the independence of the demand classes, which the paper uses without stating. Indices are 0-based in Lean (class `N - 1` is the paper's $N$).
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 635, Lemma 3

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 3: for products `j < i` (0-based), with independent demand classes, the difference of
the two "salvage" probabilities factors as a product. Empty vector conditions (when `i` is the
last class) are vacuously true. -/
theorem shortage_difference_product {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (j i : Fin N) (hji : j < i) :
    (Measure.pi ν).real
        {d | ¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1)}
      - (Measure.pi ν).real
        {d | ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)}
      = (Measure.pi ν).real {d | 0 < shortage y d (j + 1) i ∧ ShortVecZero y d j j i}
        * (Measure.pi ν).real {d | ShortVecZero y d (i + 1) (i + 1) (N - 1)} := by sorry

end BassokSubstitution
