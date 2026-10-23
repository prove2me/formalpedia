-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_proposition_1_existence
-- name    : CapitationRisk.PerfectRA.proposition_1_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:36.885909+00:00
-- url     : https://prove2.me/theorems/9f099590-2297-4092-86f5-b5455875e2ba
-- title:
--   Proposition 1 (first part), p. 18 — the MA health plan's problem (9) has a unique solution
-- statement:
--   Under the standing assumptions of the model, let $r = (r_i)_{i\in I}$ be capitation rates with $r_i \ge 0$ for all $i$. Then the health plan's problem (9),
--   $$\max_{\boldsymbol w}\ \pi(\boldsymbol w) = \sum_{i\in I}\lambda_i(\boldsymbol w)\,r_i - \sum_{s\in S}C^f_s(w_s) - \sum_{s\in S}c_s\sum_{i\in I}\lambda^s_i(w_s) \quad \text{s.t. } \underline w_s \le w_s \le 1\ \ \forall s\in S,$$
--   has exactly one solution: there is a unique MA equilibrium quality vector $\boldsymbol w^{MA}$.
--
--   This makes "the MA market equilibrium" a well-defined object, which Theorem 1 then compares with the target $\boldsymbol w^*$.
--
--   **Formalization Note.** The paper states the result "under arbitrary capitation rates". The formal statement assumes $r_i \ge 0$: with a negative rate, $\sum_i \lambda_i(\boldsymbol w) r_i$ need not be concave and uniqueness can fail. The paper's own proof uses concavity of this revenue term, which holds exactly for nonnegative rates.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 18, Proposition 1 (first sentence), problem (9)–(10); proof p. 35

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA

open Model

/-- Proposition 1 (p. 18), first sentence: for nonnegative capitation rates the health plan's
problem (9) has a unique solution. -/
theorem proposition_1_existence {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (M : Model S I) (hM : M.Standing) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃! w, M.IsMAEquilibrium r w := by sorry

end CapitationRisk.PerfectRA
