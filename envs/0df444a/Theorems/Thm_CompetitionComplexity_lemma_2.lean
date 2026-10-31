-- Prove2me | Theorems.Thm_CompetitionComplexity_lemma_2
-- name    : CompetitionComplexity.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:59.326329+00:00
-- url     : https://prove2.me/theorems/11f41a77-6857-4cc9-b312-32bb0e57f8b9
-- title:
--   Lemma 2 — $M_n(F)\le\sum_{j\ge0}\bigl(1-(\partial A_{j+1}(F)/\partial A_j(F))^n\bigr)\partial A_j(F)$
-- statement:
--   Let $F$ be a distribution on $[0,\infty)$ with finite mean and $\omega_0(F)<\omega_1(F)$, and write $\partial A_j(F)=A_{j+1}(F)-A_j(F)$. Then for every $n$,
--   $$
--   M_n(F)\le\sum_{j=0}^{\infty}\Bigl(1-\Bigl(\frac{\partial A_{j+1}(F)}{\partial A_j(F)}\Bigr)^n\Bigr)\partial A_j(F).
--   $$
--   The expected maximum of $n$ draws is thus bounded by a quantity that depends on $F$ only through the sequence $(A_j(F))$. This is one direction of the reduction to the program (1)–(4) (Theorem 3).
--
--   **Formalization Note** The series is summed in $[0,\infty]$; by Lemma 1 its terms are non-negative, so nothing is lost and no summability side condition is hidden. For $n=0$ both sides are $0$.
--
--   Differences from the source:
--   - encoding: a series of real numbers → a series in [0, ∞] of ENNReal.ofReal of the terms; reason: the terms are non-negative (Lemma 1), so the sum is the same and Lean's junk tsum of a non-summable real family is avoided
--   - encoding: Mₙ a real number → Mₙ in [0, ∞] (Mval, valued in ENNReal); reason: Mₙ is finite for every distribution, so the comparison with the series in [0, ∞] is unchanged
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Lemma 2, p.10

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Definitions.Def_CompetitionComplexity_Distribution
import Definitions.Def_CompetitionComplexity_SequenceProperties

open MeasureTheory
open CorreaThreshold.Adaptive (dpW)

namespace CompetitionComplexity

/-- **Lemma 2.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Lemma 2, p.10:
"For every distribution F with ω0(F) < ω1(F), we have
Mn(F) ≤ Σ_{j=0}^∞ (1 − (∂Aj+1(F)/∂Aj(F))^n) ∂Aj(F)."

**Formalization Note.** The series is summed in `[0, ∞]` (`ENNReal`), so no summability side
condition is hidden: under `ω₀ < ω₁` the terms are nonnegative (Lemma 1: `0 < ∂Aⱼ₊₁ ≤ ∂Aⱼ`), so
`ENNReal.ofReal` of each term is the term itself. `n` ranges over `ℕ`; at `n = 0` both sides are `0`
(`M₀ = 0`). -/
theorem lemma_2 (μ : Measure ℝ) (hμ : IsDist μ) (hω : omega0 μ < omega1 μ) (n : ℕ) :
    Mval μ n ≤ ∑' j : ℕ,
      ENNReal.ofReal ((1 - (dS (dpW μ) (j + 1) / dS (dpW μ) j) ^ n) * dS (dpW μ) j) := by sorry

end CompetitionComplexity
