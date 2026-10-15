-- Prove2me | Theorems.Thm_AccelScal_UCRace_proposition_3
-- name    : AccelScal.UCRace.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:02.699104+00:00
-- url     : https://prove2.me/theorems/7a73dab8-34ac-4f18-bc4a-406c93b9258f
-- title:
--   Proposition 3, p. 8 — best-response monotonicity and a symmetric pure Nash equilibrium
-- statement:
--   In a race of two unconstrained firms with the stated technologies, each firm's best-response set is nonempty at every positive rival intensity. If both projects are accelerable ($\gamma_1,\gamma_2>0$), then a higher rival intensity weakly raises every best response, and raises it strictly whenever the old best response exceeds the lower bound $1$. If neither project is accelerable ($\gamma_1=\gamma_2=0$), each best-response set is independent of the rival's positive intensity. When the firms have identical technology parameters, a symmetric pure-strategy Nash equilibrium exists:
--
--   $$
--   \exists R\in[1,\bar R]\quad R\in BR_1(R)\ \text{and}\ R\in BR_2(R).
--   $$
--
--   The result states when an unconstrained firm's R&D investment responds to a competitor's investment and guarantees an equilibrium for the symmetric game.
--
--   **Formalization Note** The paper writes derivatives of an optimum. Because best responses need not be unique or differentiable, these are encoded as comparisons of the full maximizer sets, with strictness at interior responses. The nonempty clauses prevent vacuous comparisons. Both $\gamma_i>0$ are needed for the increasing-response clause; symmetry requires identical technologies. The rival's intensity is allowed to be any positive value, while each firm's own feasible range is its fixed interval from (7).
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 8, Proposition 3

import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section

namespace AccelScal.UCRace

/-- Lin, Proposition 3, p. 8. Best-response derivatives are expressed as
orderings of the entire optimal sets, with strictness at interior responses. -/
theorem proposition_3 (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) :
    (∀ R2, 0 < R2 → (BR1 T1 T2 r R2).Nonempty) ∧
    (∀ R1, 0 < R1 → (BR2 T1 T2 r R1).Nonempty) ∧
    (0 < T1.γ → 0 < T2.γ →
      (∀ R2 R2', 0 < R2 → R2 < R2' →
        AccelScal.UCMonopoly.OrderedAbove (BR1 T1 T2 r R2) (BR1 T1 T2 r R2')) ∧
      (∀ R1 R1', 0 < R1 → R1 < R1' →
        AccelScal.UCMonopoly.OrderedAbove (BR2 T1 T2 r R1) (BR2 T1 T2 r R1'))) ∧
    (T1.γ = 0 → T2.γ = 0 →
      (∀ R2 R2', 0 < R2 → 0 < R2' → BR1 T1 T2 r R2 = BR1 T1 T2 r R2') ∧
      (∀ R1 R1', 0 < R1 → 0 < R1' → BR2 T1 T2 r R1 = BR2 T1 T2 r R1')) ∧
    (T1 = T2 → ∃ R, IsNash T1 T2 r R R) := by sorry

end AccelScal.UCRace
