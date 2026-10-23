-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_kernel_bound
-- name    : CapitationRisk.PerfectRA.kernel_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:32.375982+00:00
-- url     : https://prove2.me/theorems/f7d979fd-89af-4f9c-9cee-148d2c99bdb4
-- title:
--   Proof of Theorem 1, p. 36 — option-demand assumption (6) bounds each row of the pricing kernel: q_sj ≥ 0 and Σ_j q_sj ≤ 1
-- statement:
--   Under the standing assumptions of the model, for every service $s \in S$ the row $s$ of the pricing kernel of (12),
--   $$q_{sj}(\boldsymbol w^*) = \frac{\partial\lambda_j(\boldsymbol w^*)/\partial w_s}{\sum_{i\in I}\partial\lambda^s_i(w^*_s)/\partial w_s}, \qquad j \in I,$$
--   has nonnegative entries and satisfies
--   $$\sum_{j\in I} q_{sj}(\boldsymbol w^*) \le 1 .$$
--
--   The bound is the "implication of option demand theory (6)": a health plan's enrollment responds to the quality of service $s$ no more than the demand for service $s$ itself does. Combined with the no-arbitrage condition (12) it forces some capitation rate to be at least every TM price.
--
--   **Formalization Note.** The paper states only the sum bound. Nonnegativity of the entries, which follows from the health-plan demand being nondecreasing in each $w_s$, is stated in the same item because the next step of the proof needs both.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 36, proof of Theorem 1, 'and the implication of option demand theory (6), i.e., …'; assumption (6), p. 14

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA

open Model

/-- Proof of Theorem 1 (p. 36): the option-demand assumption (6) implies that every row of the
pricing kernel of (12) is nonnegative and sums to at most one. -/
theorem kernel_bound {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (M : Model S I) (hM : M.Standing) (s : S) :
    (∀ j, 0 ≤ M.kernel s j) ∧ ∑ j, M.kernel s j ≤ 1 := by sorry

end CapitationRisk.PerfectRA
