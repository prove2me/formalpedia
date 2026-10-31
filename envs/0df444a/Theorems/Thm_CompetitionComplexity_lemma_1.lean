-- Prove2me | Theorems.Thm_CompetitionComplexity_lemma_1
-- name    : CompetitionComplexity.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:58.307992+00:00
-- url     : https://prove2.me/theorems/89b90a75-f970-4351-9a9a-73c8acbe0ff9
-- title:
--   Lemma 1 — for $\omega_0(F)<\omega_1(F)$, $(A_n(F))$ satisfies (a)–(c)
-- statement:
--   Let $F$ be a distribution on $[0,\infty)$ with finite mean whose support is not a single point, i.e. $\omega_0(F)<\omega_1(F)$. Then the optimal dynamic pricing values $(A_n(F))_{n\in\mathbb N}$ satisfy:
--
--   1. **(a)** $A_n(F)$ is strictly increasing in $n$;
--   2. **(b)** the increments $\partial A_n(F)=A_{n+1}(F)-A_n(F)$ are non-increasing;
--   3. **(c)** the ratios $\partial A_{n+1}(F)/\partial A_n(F)$ are non-decreasing.
--
--   Together with $\partial A_n(F)\to0$, these are the properties that characterize the sequences $(A_n(F))$ (Lemma 3 gives the converse).
--
--   Differences from the source: none.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Lemma 1, p.9

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Definitions.Def_CompetitionComplexity_Distribution
import Definitions.Def_CompetitionComplexity_SequenceProperties

open MeasureTheory
open CorreaThreshold.Adaptive (dpW)

namespace CompetitionComplexity

/-- **Lemma 1.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Lemma 1, p.9:
"For every distribution F with ω0(F) < ω1(F), the sequence (An(F))n∈N satisfies properties (a)-(c)."

**Formalization Note.** Properties (a)–(c) of p.7 are `PropA`, `PropB`, `PropC`. -/
theorem lemma_1 (μ : Measure ℝ) (hμ : IsDist μ) (hω : omega0 μ < omega1 μ) :
    PropA (dpW μ) ∧ PropB (dpW μ) ∧ PropC (dpW μ) := by sorry

end CompetitionComplexity
