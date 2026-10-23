-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_noArbitrage_large_rate
-- name    : CapitationRisk.PerfectRA.noArbitrage_large_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:39.219335+00:00
-- url     : https://prove2.me/theorems/ac4d4b8d-0732-4280-a2bb-06b3b290ec39
-- title:
--   p. 19 — rates satisfying the no-arbitrage condition (12) include one rate r_i ≥ max_s P∗_s
-- statement:
--   Under the standing assumptions of the model, with at least one patient type, let $r = (r_i)_{i\in I}$ be nonnegative capitation rates satisfying the no-arbitrage condition (12),
--   $$\sum_{j\in I} q_{sj}(\boldsymbol w^*)\, r_j = P^*_s \quad \forall s\in S .$$
--   Then some patient type $i \in I$ has a capitation rate at least as large as every TM service price:
--   $$r_i \ge \max_{s\in S} P^*_s .$$
--
--   This is the second of the two observations from which Theorem 1 follows: rates that would induce the target must pay some patient type at least the price of the most expensive service, while the informationally perfect rates (7) pay every type strictly less than the price of a black-swan service.
--
--   **Formalization Note.** The hypothesis $r_i \ge 0$ is added; without it the bound can fail when a kernel row sums to less than one. The conclusion is stated as $\exists i\ \forall s,\ P^*_s \le r_i$, which is the paper's $r_i \ge \max_s P^*_s$.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 19, 'Second, by the implication of option demand theory (6), …'

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA

open Model

/-- p. 19: if nonnegative rates satisfy the no-arbitrage condition (12), some patient type's rate
is at least every TM service price `P∗_s`. -/
theorem noArbitrage_large_rate {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]
    (M : Model S I) (hM : M.Standing) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hna : M.NoArbitrage r) :
    ∃ i, ∀ s, M.Pstar s ≤ r i := by sorry

end CapitationRisk.PerfectRA
