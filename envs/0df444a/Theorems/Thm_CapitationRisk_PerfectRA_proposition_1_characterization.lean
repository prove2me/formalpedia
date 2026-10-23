-- Prove2me | Theorems.Thm_CapitationRisk_PerfectRA_proposition_1_characterization
-- name    : CapitationRisk.PerfectRA.proposition_1_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:44.761748+00:00
-- url     : https://prove2.me/theorems/05b4aace-b65e-4396-9bd4-275d8d3889b4
-- title:
--   Proposition 1 (second part), p. 18 — the target w∗ is the MA equilibrium iff the rates satisfy the no-arbitrage condition (12)
-- statement:
--   Under the standing assumptions of the model, suppose in addition that the targeted quality is below the top quality in every service, $w^*_s < 1$. Let $r = (r_i)_{i\in I}$ be capitation rates with $r_i \ge 0$. Then the targeted quality $\boldsymbol w^*$ solves the health plan's problem (9) if and only if the rates satisfy the no-arbitrage condition (12):
--   $$\sum_{j\in I} q_{sj}(\boldsymbol w^*)\, r_j = P^*_s \quad \forall s \in S, \qquad q_{sj}(\boldsymbol w^*) = \frac{\partial\lambda_j(\boldsymbol w^*)/\partial w_s}{\sum_{i\in I}\partial\lambda^s_i(w^*_s)/\partial w_s},$$
--   where $P^*_s = P_s(w^*_s)$ is the TM price (3) at the target.
--
--   The matrix $(q_{sj})$ is the "pricing kernel" translating per-patient MA payments into per-service TM payments: (12) says that a marginal quality change around the target earns the same marginal revenue in MA as in TM.
--
--   **Formalization Note.** Two hypotheses are added: $r_i \ge 0$ (as in the first part of Proposition 1) and $w^*_s < 1$. The latter is needed for the "only if" direction: if $w^*_s = 1$, the first-order condition at the target is only the inequality $\partial\pi/\partial w_s \ge 0$. Being "the" equilibrium is stated as being a maximizer of (9), which is equivalent by the first part of the proposition.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 18, Proposition 1 (second sentence), eq. (12); proof pp. 35–36, (27)–(28)

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA

open Model

/-- Proposition 1 (p. 18), second sentence: the targeted quality `w∗` is the MA equilibrium iff
the rates satisfy the no-arbitrage condition (12). -/
theorem proposition_1_characterization {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (M : Model S I) (hM : M.Standing) (hlt : ∀ s, M.wstar s < 1)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) :
    M.IsMAEquilibrium r M.wstar ↔ M.NoArbitrage r := by sorry

end CapitationRisk.PerfectRA
