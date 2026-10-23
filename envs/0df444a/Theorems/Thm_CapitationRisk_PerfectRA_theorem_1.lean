-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_theorem_1
-- name    : CapitationRisk.PerfectRA.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:50.909114+00:00
-- url     : https://prove2.me/theorems/b0b2a2e6-9577-4716-9b83-53aad29d0978
-- title:
--   Theorem 1, p. 19 — informationally perfect capitation rates (7) fail to achieve the targeted quality benchmark (11) in the MA market equilibrium
-- statement:
--   Consider the Medicare model under its standing assumptions, with at least one patient type, and let
--   $$r_i = \sum_{s\in S}\frac{\lambda^s_i(w^*_s)}{\lambda_i(\boldsymbol w^*)}\,P^*_s, \qquad P^*_s = P_s(w^*_s),$$
--   be the informationally perfect MA capitation rates (7), built from the TM prices (3) at the targeted quality $\boldsymbol w^*$. Assume the black-swan set (8) is nonempty: some service $s$ satisfies $P^*_s > \max_{i\in I} r_i$.
--
--   Then the MA market equilibrium under these rates exists and is unique, i.e. problem (9) has exactly one solution $\boldsymbol w^{MA}$, and it misses the Targeted Quality Benchmark (11):
--   $$\boldsymbol w^{MA} \neq \boldsymbol w^* .$$
--
--   This is the paper's first main result: even when risk adjustment is informationally perfect, so that each patient type is paid exactly its expected TM cost, the health plan does not provide the targeted quality. Risk selection therefore has a cause beyond imperfect risk adjustment.
--
--   **Formalization Note.** The rates $r_i$ and prices $P^*_s$ are the formulas (7) and (3) applied to the model, not free parameters (with free rates the statement would be false). Existence and uniqueness of the equilibrium are part of the conclusion, so the statement cannot hold vacuously. Only $w^*_s > \underline w_s$ (p. 17) is assumed of the target; $w^*_s = 1$ is allowed.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 19, Theorem 1; proof p. 36

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA

open Model

/-- Theorem 1 (p. 19): under the informationally perfect capitation rates (7) and a nonempty
black-swan set (8), the MA market equilibrium exists, is unique, and differs from the targeted
quality `w∗`, so the Targeted Quality Benchmark (11) fails. -/
theorem theorem_1 {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]
    (M : Model S I) (hM : M.Standing) (hb : M.BlackSwan) :
    ∃ wMA, M.IsMAEquilibrium M.rate wMA ∧
      (∀ w, M.IsMAEquilibrium M.rate w → w = wMA) ∧ wMA ≠ M.wstar := by sorry

end CapitationRisk.PerfectRA
