-- Prove2me | Theorems.Thm_CompetitionComplexity_lemma_4
-- name    : CompetitionComplexity.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:32.982992+00:00
-- url     : https://prove2.me/theorems/8df10438-e7d3-4c0f-ad42-3a5c11fc3845
-- title:
--   Lemma 4 — the value of the program (1)–(4) is $\varepsilon-(n-1)\rho_{\varepsilon,m}^n$
-- statement:
--   Let $\varepsilon>0$, let $n\ge2$ and $m\ge3$ be integers, and assume $\rho_{\varepsilon,m}$ of the recursion (9) is well defined. Then the optimal value of the program (1)–(4),
--   $$
--   \inf\Bigl\{(1+\varepsilon)\sum_{i=0}^{m-1}\delta_i-\sum_{i=0}^{\infty}\Bigl(1-\Bigl(\frac{\delta_{i+1}}{\delta_i}\Bigr)^n\Bigr)\delta_i\ :\ \delta\ \text{satisfies (2)–(4)}\Bigr\},
--   $$
--   equals
--   $$
--   \varepsilon-(n-1)\rho_{\varepsilon,m}^{\,n}.
--   $$
--   Combined with Theorem 3, $(1+\varepsilon)A_m(F)\ge M_n(F)$ holds for every $F$ exactly when $(n-1)\rho_{\varepsilon,m}^n\le\varepsilon$, which turns the competition complexity into a question about the recursion (9).
--
--   **Formalization Note** The value is stated as the greatest lower bound of the objective's values on the feasible set; it is in general not attained.
--
--   Differences from the source:
--   - encoding: the value of (1)–(4) is equal to ε − (n − 1)ρⁿ_{ε,m} → IsGLB of the objective's image of the feasible set at ε − (n − 1)ρⁿ_{ε,m}; reason: the value is an infimum that need not be attained; avoids Lean's junk sInf
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Lemma 4, p.20

import Mathlib
import Definitions.Def_CompetitionComplexity_Program
import Definitions.Def_CompetitionComplexity_Recursion

namespace CompetitionComplexity

/-- **Lemma 4** (the value of the program).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Lemma 4, p.20:
"Let ε > 0, and let n ≥ 2 and m ≥ 3 be two positive integers such that ρε,m is well defined. Then,
the value of the optimization problem (1)-(4) is equal to ε − (n − 1)ρ^n_{ε,m}."

**Formalization Note.** "The value" is the infimum of the objective (1) over the feasible set
(2)–(4), stated as `IsGLB` (the infimum is in general not attained). -/
theorem lemma_4 (ε : ℝ) (hε : 0 < ε) (n m : ℕ) (hn : 2 ≤ n) (hm : 3 ≤ m) (hw : WellDef ε n m) :
    IsGLB (objective ε n m '' {δ | Feasible δ}) (ε - ((n : ℝ) - 1) * rho ε n m ^ n) := by sorry

end CompetitionComplexity
