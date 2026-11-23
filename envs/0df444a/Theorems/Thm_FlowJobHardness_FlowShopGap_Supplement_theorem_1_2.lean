-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_Supplement_theorem_1_2
-- name    : FlowJobHardness.FlowShopGap.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:27:13.073348+00:00
-- url     : https://prove2.me/theorems/5543300f-6568-4c0b-9391-38257cd181ae
-- title:
--   Theorem 1.2 — NP-hard bounded-operation generalized-flow-shop half-jobs gap
-- statement:
--   There is an integer threshold $K_0$ such that for every fixed integer $K\ge K_0$ there is an operation-count bound $B(K)$ for which it is NP-hard under deterministic polynomial-time many-one reductions to distinguish the following generalized flow shops:
--   $$\begin{aligned}\mathrm{YES}:&\quad \exists s\text{ feasible},\quad C_{\max}(s)\le2K\,\mathrm{lb},\\\mathrm{NO}:&\quad \forall s\text{ feasible},\quad |\{j:C_j(s)\le K^{(\log_2 K)/25}\mathrm{lb}/8\}|\le n/2.\end{aligned}$$
--   Both sides have at most $B(K)$ operations in every job; $B$ depends on $K$ alone, never on the input size. The NO side excludes YES, making a disjoint promise even on empty inputs. Within-time endpoints are inclusive; more-than-half uses a strict integer majority.
--
--   This companion theorem gives the computational gap underlying constant-factor inapproximability, rather than only the published mathematical construction gap.
--
--   Differences from the source:
--   - encoding: Polynomial-time scheduling and standard machine complexity classes are stated without a concrete bit syntax. → Use binary rational instances and schedule outputs, published bounded Turing machines and genuine NP reductions; compare against every feasible real-time schedule.; reason: Specify the standard finite-input meaning while retaining zero durations, repeated visits and all comparison schedules.
--   - encoding: The NP-hard YES/NO distinction is stated for sufficiently large fixed K; empty jobs are not discussed. → K is a natural color-count parameter, with an existential K0; logarithms in the exact gap are base two; NO excludes YES explicitly.; reason: The proof on p. 20:12 uses integer color counts and fixed-K bounded degrees. Empty zero-load shops would otherwise lie in both cases and admit a constant fake reduction; the nonempty hard instances are unaffected.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:5, Theorem 1.2

import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Algorithms
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

theorem theorem_1_2 :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ B : ℕ,
      MeanBudgetXC.Supplement.PromiseNPHard (halfGapYes K B) (halfGapNo K B) := by sorry

end FlowJobHardness.FlowShopGap.Supplement
